/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.PrivateResolutionForkSourceEquilibrium
import Vegas.Source.DisclosureBehavioral
import GameTheoryExtensions.Analysis.Protocol.BehavioralContinuity

/-! # Bob's actual normalized source law

Bob has no earlier source decision in this program. Alice's foreign disclosure
does not modify his restored action list, and his authentic initial TRUE
binding makes both of his disclosure intentions effective. Normalization
therefore retains his actual original source lottery at either publication.
The convergence result uses the actual original source decision site, not a
native posterior or a native fixture path probability.
-/

noncomputable section

namespace Vegas.PrivateResolutionFork

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Math.Probability Filter

/-- The real behavioral disclosure normalizer preserves Bob's entire current
Bool lottery. It never conditions Bob on Alice's hidden disclosure intention. -/
theorem normalized_bob_choice (profile : BehavioralProfile setup.program)
    (high disclose : Bool) :
    (normalizeDisclosureProfile setup.program [] (Revelations.initial setup.context)
      profile bob).2.1 rfl ((sourceAliceDone high disclose).view bob) =
      (profile bob).2.1 rfl ((sourceAliceDone high disclose).view bob) := by
  dsimp only [normalizeDisclosureProfile, BehavioralPolicy.normalizeDisclosures, setup, program,
    BehavioralPolicy.normalizeDisclosureFrom]
  simp only [dite_eq_right (by decide : alice ≠ bob), DecisionView.back,
    Bool.false_eq_true, ite_false, disclosureMemoryLaw, PMF.pure_bind, PMF.map_comp]
  change ((profile bob).2.1 rfl ((sourceAliceDone high disclose).view bob)).map
    (fun intended => effectiveDisclosure 5
      (.there (.there (.there (.there .here)))) (sourceAliceDone high disclose) intended) = _
  have identity (intended : Bool) : effectiveDisclosure 5
      (.there (.there (.there (.there .here)))) (sourceAliceDone high disclose) intended =
      intended := by
    cases high <;> cases disclose <;> cases intended <;> decide
  simp only [identity]
  exact PMF.map_id _

/-- Decoding a genuine source behavioral policy and normalizing disclosure
retains its actual Bob protocol choice at the observed publication. -/
theorem normalized_decoded_bob_choice
    (profile : Profile sourceModel.behavioralSignature) (high disclose : Bool) :
    (normalizeDisclosureProfile setup.program [] (Revelations.initial setup.context)
      (setup.decodeBehavioralProfile sourceAdmission profile) bob).2.1 rfl
        ((sourceAliceDone high disclose).view bob) =
      sourceChoiceDisclosure bob (sourceBobInput disclose)
        (profile bob (sourceBobInput disclose)) := by
  rw [normalized_bob_choice]
  change (profile bob (setup.protocolObserve bob (SourcePosition.guessed high disclose).state)).map
    (fun choice => OwnAction.disclosure choice.1) = _
  rw [source_bob_input]
  rfl

/-- Each literal Bob input is an actual legal source decision site. -/
theorem exists_source_bob_site (disclose : Bool) :
    ∃ site : sourceModel.InformationSite bob, site.1 = sourceBobInput disclose := by
  have selected : (SourcePosition.guessed true disclose).state ∈
      ((sourceModel.runBehavioral uniformSourceProfile 4).map
        ExecutionProtocol.History.state).support := by
    rw [uniformSourceProfile, source_initialized_bob_law]
    apply mem_support_mix_left _ _ _ (by norm_num)
    rw [PMF.support_map]
    exact ⟨disclose, PMF.mem_support_uniformOfFintype _, rfl⟩
  obtain ⟨history, _reached, same⟩ := PMF.support_map .. ▸ selected
  have active : sourceArena.active history.state bob := by
    rw [same]
    rfl
  have running : ¬ sourceArena.terminal history.state := by
    rw [same]
    exact not_false
  obtain ⟨site, seen⟩ := sourceModel.exists_informationSite_of_active bob history running active
  refine ⟨site, seen.trans ?_⟩
  rw [source_history_observe, same, source_bob_input]

/-- Every genuinely converging original source assessment sequence has a
normalized Bob LOW limit at TRUE, including arbitrary fully supported source
sequences returned before the native waiting rates are chosen. -/
theorem normalized_decoded_bob_low_converges
    (sequence : Nat → sourceModel.BehavioralAssessment)
    (target : sourceModel.BehavioralAssessment)
    (converges : InformationModel.BehavioralAssessmentConvergesPointwise sequence target)
    (strategy : target.strategy = sourceEquilibriumProfile) (high : Bool) :
    PMFConvergesPointwise
      (fun n => (normalizeDisclosureProfile setup.program []
        (Revelations.initial setup.context)
        (setup.decodeBehavioralProfile sourceAdmission (sequence n).strategy) bob).2.1 rfl
          ((sourceAliceDone high true).view bob)) (PMF.pure false) := by
  obtain ⟨site, observed⟩ := exists_source_bob_site true
  have law := (converges.strategy bob site).map
    (fun choice => OwnAction.disclosure choice.1)
  rw [observed] at law
  change PMFConvergesPointwise
    (fun n => sourceChoiceDisclosure bob (sourceBobInput true)
      ((sequence n).strategy bob (sourceBobInput true)))
    (sourceChoiceDisclosure bob (sourceBobInput true)
      (target.strategy bob (sourceBobInput true))) at law
  rw [strategy, source_equilibrium_bob_choice] at law
  simpa only [normalized_decoded_bob_choice, Bool.not_true] using law

end Vegas.PrivateResolutionFork
