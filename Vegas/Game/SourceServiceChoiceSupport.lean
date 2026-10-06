/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceChoiceCompletion
import Vegas.Game.SourceServiceAdmission
import GameTheoryExtensions.Math.Probability.Support

/-! # Source choice support for the concrete full-source service

The existing message bounds already cover every fresh binding value. They
therefore supply precisely the finite source alphabets needed to complete
unreachable information values. Initial parameters, public samples and
publication payload types are not required to be finite.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime
open GameTheory GameTheory.Protocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

private theorem finiteBindingTypes_of_outputs :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) →
    (∀ event owner payload, outputLayout program event = .binding owner payload →
      Finite (L.Val payload)) → program.FiniteBindingTypes
  | _, _, .ret _, _ => trivial
  | _, _, .sample _ _ _ next, finite =>
      finiteBindingTypes_of_outputs next (fun event owner payload kind =>
        finite event.succ owner payload kind)
  | _, _, .commit (payload := payload) _ owner _ _ next, finite =>
      ⟨finite ⟨0, by simp [eventCount]⟩ owner payload rfl,
        finiteBindingTypes_of_outputs next (fun event owner payload kind =>
          finite event.succ owner payload kind)⟩
  | _, _, .reveal _ _ _ _ _ _ next, finite =>
      finiteBindingTypes_of_outputs next (fun event owner payload kind =>
        finite event.succ owner payload kind)

/-- The compiler's existing finite binding-value coverage supplies source
choice finiteness without strengthening the source or native game. -/
theorem sourceService_finiteBindingTypes (setup : Setup (Player := Player) (L := L))
    {mode : EventGraph.ExecutionMode} (bounds : MessageBounds (serviceGraph setup mode))
    (covered : bounds.CoversBindingValues) :
    setup.program.FiniteBindingTypes :=
  finiteBindingTypes_of_outputs setup.program (fun event owner payload kind =>
    bounds.finite_binding_values covered event owner payload kind)

/-- Full support of an original source policy at abstract views supplies all
effective guarded choices to the actual compiler, through its existing
conditional private-memory normalization. -/
theorem sourceService_normalized_support
    (setup : Setup (Player := Player) (L := L))
    (profile : Profile (setup.informationModel
      (CommitmentInterface.values setup.program)).behavioralSignature)
    (full : ∀ who info, FullSupport (profile who info)) (who : Player) :
    (normalizeDisclosureProfile setup.program [] (Revelations.initial setup.context)
      (setup.decodeBehavioralProfile (CommitmentInterface.values setup.program) profile)
        who).SupportsEffectiveChoices setup.program (CommitmentInterface.values setup.program)
          [] (Revelations.initial setup.context) := by
  apply normalizeDisclosureProfile_supports
  intro player
  exact BehavioralPolicy.fromProtocol_supports setup.program
    (CommitmentInterface.values setup.program) _ (fun view => full player (some view))

/-- Every original consistent source assessment has a single completed Bayes
sequence whose normalized policies support every effective service choice.
The original assessment remains the limit. All finiteness follows from the
already declared coverage of new binding values by the actual native bounds. -/
theorem sourceService_consistent_supported_sequence [Fintype Player]
    (setup : Setup (Player := Player) (L := L))
    (bounds : MessageBounds (graph setup)) (covered : bounds.CoversBindingValues)
    (assessment : (setup.informationModel
      (CommitmentInterface.values setup.program)).BehavioralAssessment)
    (antichain : (setup.informationModel
      (CommitmentInterface.values setup.program)).DecisionInformationAntichain)
    (consistent : assessment.IsSequentiallyConsistent antichain) :
    ∃ sequence : Nat → (setup.informationModel
        (CommitmentInterface.values setup.program)).BehavioralAssessment,
      (∀ n who info, FullSupport ((sequence n).strategy who info)) ∧
      (∀ n, InformationModel.BehavioralAssessment.IsBayesConsistent
        (setup.informationModel (CommitmentInterface.values setup.program))
        (sequence n) antichain) ∧
      InformationModel.BehavioralAssessmentConvergesPointwise sequence assessment ∧
      (∀ n who, (normalizeDisclosureProfile setup.program [] (Revelations.initial setup.context)
        (setup.decodeBehavioralProfile (CommitmentInterface.values setup.program)
          (sequence n).strategy) who).SupportsEffectiveChoices setup.program
            (CommitmentInterface.values setup.program) [] (Revelations.initial setup.context)) := by
  obtain ⟨sequence, full, bayes, converges⟩ := setup.exists_complete_consistent_sequence
    (sourceService_finiteBindingTypes setup bounds covered)
    (CommitmentInterface.values setup.program) assessment antichain consistent
  exact ⟨sequence, full, bayes, converges,
    fun n who => sourceService_normalized_support setup (sequence n).strategy (full n) who⟩

end Vegas
