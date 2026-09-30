/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.ProtocolChoiceFiniteness
import Vegas.Source.DisclosureSupport
import Vegas.Game.SourceContinuation
import GameTheory.Protocol.DecisionPlan
import GameTheory.Protocol.FiniteInformation
import GameTheory.Analysis.Protocol.Sequential
import GameTheoryExtensions.Math.Probability.Support
import GameTheoryExtensions.Math.Probability.Uniform

/-! # Completing unreachable source choices before normalization

Uniform fallback is used only outside actual decision information sites.
Every legal continuation and every assessment coordinate stays unchanged.
Finite fresh-binding alphabets suffice; no finite information carrier or
finite initial/public value type is required.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

def completeChoices (setup : Setup (Player := Player) (L := L))
    (finite : setup.program.FiniteBindingTypes) (admission : CommitmentInterface setup.program)
    (profile : Profile (setup.informationModel admission).behavioralSignature) :
    Profile (setup.informationModel admission).behavioralSignature := fun who =>
  (profile who).restrictToDecisions.extend (fun info => by
    let := setup.finite_choice finite admission who info
    let := Fintype.ofFinite ((setup.informationModel admission).Choice who info)
    let : Nonempty ((setup.informationModel admission).Choice who info) :=
      ⟨(profile who info).support_nonempty.choose⟩
    exact (PMF.uniformOfFintype _))

theorem completeChoices_site (setup : Setup (Player := Player) (L := L))
    (finite : setup.program.FiniteBindingTypes) (admission : CommitmentInterface setup.program)
    (profile : Profile (setup.informationModel admission).behavioralSignature)
    (who : Player) (site : (setup.informationModel admission).InformationSite who) :
    setup.completeChoices finite admission profile who site.1 = profile who site.1 :=
  (profile who).restrictToDecisions.extend_site _ site

/-- Full mixing at actual sites, together with the uniform fallback, gives
full support at every abstract information value used by private memory. -/
theorem completeChoices_fullSupport (setup : Setup (Player := Player) (L := L))
    (finite : setup.program.FiniteBindingTypes) (admission : CommitmentInterface setup.program)
    (assessment : (setup.informationModel admission).BehavioralAssessment)
    (mixed : assessment.IsFullyMixed) (who : Player) (info : setup.ProtocolView who) :
    FullSupport (setup.completeChoices finite admission assessment.strategy who info) := by
  classical
  let := setup.finite_choice finite admission who info
  let := Fintype.ofFinite ((setup.informationModel admission).Choice who info)
  let : Nonempty ((setup.informationModel admission).Choice who info) :=
    ⟨(assessment.strategy who info).support_nonempty.choose⟩
  unfold completeChoices InformationModel.BehavioralDecisionPlan.extend
  split
  · rename_i available
    exact mixed who ⟨info, available⟩
  · exact PMF.mem_support_uniformOfFintype

/-- The completed syntax policy supports every legal source constructor
choice, so disclosure normalization retains every effective native choice. -/
theorem completeChoices_supports (setup : Setup (Player := Player) (L := L))
    (finite : setup.program.FiniteBindingTypes) (admission : CommitmentInterface setup.program)
    (assessment : (setup.informationModel admission).BehavioralAssessment)
    (mixed : assessment.IsFullyMixed) (who : Player) :
    (setup.decodeBehavioralProfile admission
      (setup.completeChoices finite admission assessment.strategy) who).SupportsChoices
        setup.program admission :=
  BehavioralPolicy.fromProtocol_supports setup.program admission _
    (fun view => setup.completeChoices_fullSupport finite admission assessment mixed who
      (some view))

theorem completeChoices_runBehavioralFrom [Fintype Player]
    (setup : Setup (Player := Player) (L := L))
    (finite : setup.program.FiniteBindingTypes) (admission : CommitmentInterface setup.program)
    (profile : Profile (setup.informationModel admission).behavioralSignature)
    (fuel : Nat) (history : (setup.executionProtocol admission).History) :
    (setup.informationModel admission).runBehavioralFrom
      (setup.completeChoices finite admission profile) fuel history =
        (setup.informationModel admission).runBehavioralFrom profile fuel history :=
  InformationModel.runBehavioralFrom_extend_restrict profile _ fuel history

def completeChoiceAssessment (setup : Setup (Player := Player) (L := L))
    (finite : setup.program.FiniteBindingTypes) (admission : CommitmentInterface setup.program)
    (assessment : (setup.informationModel admission).BehavioralAssessment) :
    (setup.informationModel admission).BehavioralAssessment :=
  { assessment with strategy := setup.completeChoices finite admission assessment.strategy }

/-- One original consistent sequence can be completed pointwise without
changing its limiting assessment or selecting a different subsequence. -/
theorem completeChoiceAssessment_converges
    (setup : Setup (Player := Player) (L := L))
    (finite : setup.program.FiniteBindingTypes) (admission : CommitmentInterface setup.program)
    (sequence : Nat → (setup.informationModel admission).BehavioralAssessment)
    (target : (setup.informationModel admission).BehavioralAssessment)
    (converges : InformationModel.BehavioralAssessmentConvergesPointwise sequence target) :
    InformationModel.BehavioralAssessmentConvergesPointwise
      (fun n => setup.completeChoiceAssessment finite admission (sequence n)) target := by
  refine ⟨?_, converges.2⟩
  intro who site
  have equal : (fun n => (setup.completeChoiceAssessment finite admission (sequence n)).strategy
      who site.1) = fun n => (sequence n).strategy who site.1 := by
    funext n
    exact setup.completeChoices_site finite admission (sequence n).strategy who site
  rw [equal]
  exact converges.1 who site

theorem completeChoices_historyReachWeight [Fintype Player]
    (setup : Setup (Player := Player) (L := L))
    (finite : setup.program.FiniteBindingTypes) (admission : CommitmentInterface setup.program)
    (profile : Profile (setup.informationModel admission).behavioralSignature)
    (history : (setup.executionProtocol admission).History) :
    (setup.informationModel admission).historyReachWeight
      (setup.completeChoices finite admission profile) history =
        (setup.informationModel admission).historyReachWeight profile history := by
  unfold InformationModel.historyReachWeight InformationModel.runBehavioral
  rw [setup.completeChoices_runBehavioralFrom]

theorem completeChoices_informationMass [Fintype Player]
    (setup : Setup (Player := Player) (L := L))
    (finite : setup.program.FiniteBindingTypes) (admission : CommitmentInterface setup.program)
    (profile : Profile (setup.informationModel admission).behavioralSignature)
    (who : Player) (site : (setup.informationModel admission).InformationSite who) :
    (setup.informationModel admission).informationMass
      (setup.completeChoices finite admission profile) who site =
        (setup.informationModel admission).informationMass profile who site := by
  unfold InformationModel.informationMass
  simp_rw [setup.completeChoices_historyReachWeight]

/-- Completing unreachable choices preserves Bayes' rule, including the
positive-mass condition at every actual information site. -/
theorem completeChoiceAssessment_bayes [Fintype Player]
    (setup : Setup (Player := Player) (L := L))
    (finite : setup.program.FiniteBindingTypes) (admission : CommitmentInterface setup.program)
    (assessment : (setup.informationModel admission).BehavioralAssessment)
    (antichain : (setup.informationModel admission).DecisionInformationAntichain)
    (bayes : InformationModel.BehavioralAssessment.IsBayesConsistent
      (setup.informationModel admission) assessment antichain) :
    InformationModel.BehavioralAssessment.IsBayesConsistent
      (setup.informationModel admission)
      (setup.completeChoiceAssessment finite admission assessment) antichain := by
  intro who site positive history
  change 0 < (setup.informationModel admission).informationMass
    (setup.completeChoices finite admission assessment.strategy) who site at positive
  rw [setup.completeChoices_informationMass] at positive
  change assessment.belief who site history =
    (setup.informationModel admission).historyReachWeight
      (setup.completeChoices finite admission assessment.strategy) history /
      (setup.informationModel admission).informationMass
        (setup.completeChoices finite admission assessment.strategy) who site
  rw [setup.completeChoices_historyReachWeight, setup.completeChoices_informationMass]
  exact bayes who site positive history

/-- The original consistent assessment admits one Bayes sequence with full
support at every abstract source view. Its limit is the original assessment;
only strategy coordinates outside actual decision sites are completed. -/
theorem exists_complete_consistent_sequence [Fintype Player]
    (setup : Setup (Player := Player) (L := L))
    (finite : setup.program.FiniteBindingTypes) (admission : CommitmentInterface setup.program)
    (assessment : (setup.informationModel admission).BehavioralAssessment)
    (antichain : (setup.informationModel admission).DecisionInformationAntichain)
    (consistent : assessment.IsSequentiallyConsistent antichain) :
    ∃ sequence : Nat → (setup.informationModel admission).BehavioralAssessment,
      (∀ n who info, FullSupport ((sequence n).strategy who info)) ∧
      (∀ n, InformationModel.BehavioralAssessment.IsBayesConsistent
        (setup.informationModel admission) (sequence n) antichain) ∧
      InformationModel.BehavioralAssessmentConvergesPointwise sequence assessment := by
  obtain ⟨sequence, regular, converges⟩ := consistent
  refine ⟨fun n => setup.completeChoiceAssessment finite admission (sequence n), ?_, ?_,
    setup.completeChoiceAssessment_converges finite admission sequence assessment converges⟩
  · intro n who info
    exact setup.completeChoices_fullSupport finite admission (sequence n) (regular n).1 who info
  · intro n
    exact setup.completeChoiceAssessment_bayes finite admission (sequence n) antichain
      (regular n).2

end Vegas.SourceProgram.Setup
