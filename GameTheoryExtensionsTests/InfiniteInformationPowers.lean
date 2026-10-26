/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions.Analysis.Protocol.PowerCompleteness

/-! # Certificate extraction with infinitely many unused information values

Only information zero is a decision, and information one is terminal. All
other natural-number information values are unused. The actual legal history
carrier is finite; the ambient information carrier is provably infinite.
-/

noncomputable section

namespace GameTheoryExtensionsTests.InfiniteInformationPowers

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability

@[reducible] def arena : ExecutionProtocol Unit where
  State := Bool
  Action _ := Bool
  init := false
  active state _ := state = false
  available _ _ := Set.univ
  terminal state := state = true
  step _ _ := PMF.pure true
  progress state running := by
    refine ⟨fun _ => some false, fun _ => ?_⟩
    cases state <;> simp_all

@[reducible] def signals : InfoSignals arena where
  PublicSignal := Bool
  PrivateSignal _ := Unit
  initialPublic := false
  initialPrivate _ := ()
  publicSignal event := event.target
  privateSignal _ _ := ()
  InfoState _ := Nat
  initInfo _ _ state := if state then 1 else 0
  pushInfo _ _ _ _ state := if state then 1 else 0

theorem info_state (who : Unit) {state} (trace : arena.Trace state) :
    signals.infoOf who trace = if state then 1 else 0 := by
  cases trace <;> rfl

@[reducible] def model : InformationModel arena where
  toInfoSignals := signals
  menu _ info := if info = 0 then {choice | ∃ action, choice = some action} else {none}
  menu_adequate who state trace choice := by
    rw [info_state]
    cases state <;> cases choice <;> simp [LegalOption, arena]

instance (who : Unit) (info : Nat) : Fintype (model.Choice who info) := Fintype.ofFinite _

instance (who : Unit) (info : Nat) : Nonempty (model.Choice who info) := by
  by_cases zero : info = 0
  · exact ⟨⟨some false, by simp [zero]⟩⟩
  · exact ⟨⟨none, by simp [zero]⟩⟩

def uniformStrategy (who : Unit) (info : model.InfoState who) : PMF (model.Choice who info) :=
  PMF.uniformOfFintype _

theorem uniform_full (who : Unit) (site : model.InformationSite who)
    (choice : model.Choice who site.1) : choice ∈ (uniformStrategy who site.1).support :=
  PMF.mem_support_uniformOfFintype choice

theorem bounded : arena.BoundedHorizon 1 := by
  intro state trace long
  cases trace with
  | start => simp [Trace.length] at long
  | extend prior joint legal realized =>
    exact (PMF.mem_support_pure_iff _ _).mp realized

theorem false_trace_depth {state} (trace : arena.Trace state) (same : state = false) :
    trace.length = 0 := by
  refine @Trace.rec Unit arena (fun state trace => state = false → trace.length = 0)
    (fun _ => rfl) ?_ state trace same
  intro source target prior joint legal realized _ equal
  have targetTrue : target = true := (PMF.mem_support_pure_iff _ _).mp realized
  exact Bool.noConfusion (equal.symm.trans targetTrue)

theorem site_depth (who : Unit) (site : model.InformationSite who)
    (history : model.InformationHistory who site.1) : history.1.trace.length = 0 :=
  false_trace_depth history.1.trace (InformationSite.active model site history)

theorem antichain : model.DecisionInformationAntichain := by
  intro who site first second joint legal reached realized fuel reach
  have monotone := reach.trace_length_le
  change first.1.trace.length + 1 ≤ second.1.trace.length at monotone
  rw [site_depth who site first, site_depth who site second] at monotone
  omega

private local instance : Finite arena.History :=
  (model.bayesAssessment_isFullyMixed uniformStrategy uniform_full antichain).finite_history
    bounded (fun _ _ => Set.toFinite _) (fun _ => Set.toFinite _)

def assessment : model.BehavioralAssessment :=
  model.bayesAssessment uniformStrategy uniform_full antichain

theorem consistent : assessment.IsSequentiallyConsistent antichain :=
  BehavioralAssessment.IsSequentiallyConsistent.of_fullyMixed_bayes antichain
    (model.bayesAssessment_isFullyMixed uniformStrategy uniform_full antichain)
    (model.bayesAssessment_isBayesConsistent uniformStrategy uniform_full antichain)

theorem ambient_information_infinite : Infinite (model.InfoState ()) :=
  inferInstanceAs (Infinite Nat)

/-- Actual finite histories suffice even though ambient information is infinite. -/
theorem exact_assessment_has_certificate :
    ∃ (coefficient : ∀ who info, model.Choice who info → ℝ)
      (order : ∀ who info, model.Choice who info → Nat)
      (reference : ∀ who (site : model.InformationSite who), model.InformationHistory who site.1),
      (∀ who info choice, 0 < coefficient who info choice) ∧
      (∀ who info choice,
        (if order who info choice = 0 then coefficient who info choice else 0) =
          (assessment.strategy who info choice).toReal) ∧
      (∀ who (site : model.InformationSite who) (history : model.InformationHistory who site.1),
        model.powerHistoryOrder order (reference who site).1.trace ≤
          model.powerHistoryOrder order history.1.trace) ∧
      (∀ who (site : model.InformationSite who) (history : model.InformationHistory who site.1),
        model.powerHistoryOrder order history.1.trace =
            model.powerHistoryOrder order (reference who site).1.trace ↔
          (assessment.belief who site history).toReal ≠ 0) ∧
      (∀ who (site : model.InformationSite who) (history : model.InformationHistory who site.1),
        (assessment.belief who site history).toReal ≠ 0 →
        model.powerHistoryCoefficient coefficient history.1.trace /
            model.powerHistoryCoefficient coefficient (reference who site).1.trace =
          (assessment.belief who site history).toReal /
            (assessment.belief who site (reference who site)).toReal) := by
  exact consistent.exists_power_certificate model

end GameTheoryExtensionsTests.InfiniteInformationPowers
