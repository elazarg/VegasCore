/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions.Analysis.Protocol.SourceGainTransport
import GameTheoryExtensionsTests.RestrictionEnforcement

/-! # A sunk fee leaves the responder indifferent

The fee is zero before entry and one after entry, so utility is not globally
constant. Once the responder acts, either answer retains the same fee. Every
assessment and whole-policy alternative therefore has zero gain at that site.
-/

noncomputable section

namespace GameTheoryExtensionsTests.ContinuationIndifference

open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Protocol.ExecutionProtocol
open RestrictionEnforcement

def fee (history : (arena true).History) (_who : Bool) : ℝ := charge history false

theorem fee_varies_with_history :
    fee (arena true).initHistory true = 0 ∧ fee (responseHistory true rfl) true = 1 := by
  constructor <;> rfl

/-- A genuine later decision cannot alter a fee incurred at entry, even for
an assessment with arbitrary beliefs or an arbitrary continuation policy. -/
theorem response_gain_eq_zero (assessment : (model true).BehavioralAssessment)
    (alternative : (model true).BehavioralPolicy true) :
    expect ((model true).assessmentComparisonWith
        (fun players => (model true).runBehavioralFrom players 1) id assessment true
        (bobSite, alternative)).alternative (fee · true) -
      expect ((model true).assessmentComparisonWith
        (fun players => (model true).runBehavioralFrom players 1) id assessment true
        (bobSite, alternative)).prescribed (fee · true) = 0 := by
  apply (model true).gain_eq_zero_of_constant_continuations _ id fee assessment
    (bobSite, alternative) (fun _ => 1)
  intro history players final supported
  have start : history.1.state = .response := by
    have observed := history.2
    have atSite : bobSite.val = .response := info_state true true _
    simpa only [info_state] using observed.trans atSite
  have zero : (model true).runBehavioralFrom players 0 = PMF.pure := funext fun _ => rfl
  rw [(model true).runBehavioralFrom_succ_localStep, zero, PMF.bind_pure] at supported
  obtain ⟨choices, _, reached⟩ := (PMF.mem_support_bind_iff ..).mp supported
  have mapped : final.state ∈ (((model true).localStep history.1 choices).map
      History.state).support := by
    rw [PMF.support_map]
    exact ⟨final, reached, rfl⟩
  rw [localStep_state] at mapped
  let chosen : Bool → Option Bool := fun who => (choices who).1
  change final.state ∈ (if RestrictionEnforcement.terminal history.1.state then
    PMF.pure history.1.state
    else transition history.1.state chosen).support at mapped
  rw [start] at mapped
  have state : final.state = .done (some ((chosen true).getD false)) := by
    simpa only [RestrictionEnforcement.terminal, ↓reduceIte, transition,
      PMF.mem_support_pure_iff] using mapped
  simp only [id_eq, fee, charge, Bool.false_eq_true, ↓reduceIte, state]

end GameTheoryExtensionsTests.ContinuationIndifference
