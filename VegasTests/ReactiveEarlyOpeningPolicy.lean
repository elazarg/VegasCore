/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.ReactiveEarlyOpeningEvaluation

/-! # The actual graph-policy compiler in the early-opening continuation -/

noncomputable section

namespace VegasTests.ReactiveEarlyOpening

open GameTheory GameTheory.Protocol GameTheory.Math.Probability Interaction
open Vegas Vegas.EventGraphRuntime

def zeroPolicy : graph.BehavioralPolicy () := fun event =>
  Fin.cases (fun _ _ => FinDist.pure (.success 0)) (fun _ _ _ => FinDist.pure true) event

def compiled : app.Policy := runtime.compileReactivePolicy leaks () zeroPolicy

theorem zeroPolicy_resolve (actor : graph.actor? 1 = some ())
    (observation : graph.PlayerObservation ()) : zeroPolicy 1 actor observation =
      FinDist.pure true := rfl

theorem prescribed_initial :
    runtime.prescribedReactivePolicy leaks () zeroPolicy [] ((activated initial).observe app ()) =
      FinDist.pure (runtime.reactiveDecision leaks () 0 (.success 0)
        ((activated initial).observe app ()).application) := by
  have grant : ((activated initial).observe app ()).application.publicView.serviceGrant =
      some 0 := rfl
  have ready : ((activated initial).observe app ()).application.publicView.EventReady 0 := by
    decide
  have actor : graph.actor? 0 = some () := rfl
  rw [prescribedReactivePolicy_apply]
  simp only [prescribedReactiveResponse, grant, reactiveAlreadySubmitted, List.any_nil,
    Bool.false_eq_true, ite_false, dite_true, ite_eq_left ready, dite_eq_left actor,
    EventGraph.normalizePolicy, zeroPolicy, Fin.cases_zero, FinDist.map_pure,
    FinDist.bind_const]

theorem first_inconsistent :
    ¬ (runtime.prescribedReactivePolicy leaks () zeroPolicy).Consistent
      ((afterFirst first).recall ()) := by
  intro valid
  change ReactiveApplication.Policy.Consistent _ ([] ++ [_]) at valid
  have supported := (ReactiveApplication.Policy.consistent_snoc_iff _ [] _).mp valid
  have selected := supported.2
  change first ∈ (runtime.prescribedReactivePolicy leaks () zeroPolicy []
    ((activated initial).observe app ())).support at selected
  rw [prescribed_initial] at selected
  have same := FinDist.mem_support_pure.mp selected
  have sent := congrArg ReactiveApplication.Action.transmission same
  have slot : reactiveFreshSlot ((activated initial).observe app ()).application = some 0 := by
    unfold reactiveFreshSlot
    split
    · congr 1
      exact (Nat.find_eq_zero _).mpr rfl
    · rename_i impossible
      exact False.elim (impossible ⟨0, rfl⟩)
  change some (ReactiveApplication.Transmission.submit (app := app)
      ⟨.commitment 0 ((), .prepared 0), some ⟨.int, 1⟩⟩) =
    (reactiveFreshSlot ((activated initial).observe app ()).application).map _ at sent
  rw [slot] at sent
  have material := ReactiveApplication.Transmission.submit.inj (Option.some.inj sent)
  have opening := congrArg Submission.opening material
  have raw := Option.some.inj opening
  have value := congrArg (fun raw : Raw simpleExpr => raw.as? .int) raw
  cases value

theorem inconsistent_of_first (history : List app.PlayerEntry)
    (retained : (afterFirst first).recall () <+: history) :
    ¬ (runtime.prescribedReactivePolicy leaks () zeroPolicy).Consistent history := by
  obtain ⟨tail, rfl⟩ := retained
  exact fun valid => first_inconsistent valid.of_append

theorem contested_inconsistent :
    ¬ (runtime.prescribedReactivePolicy leaks () zeroPolicy).Consistent (contested.recall ()) :=
  inconsistent_of_first _ (app.respond_recall_prefix (activated (afterFirst first)) () () second)

theorem recovery_slot :
    reactiveFreshSlot ((activated contested).observe app ()).application = some 1 := by
  unfold reactiveFreshSlot
  split
  · congr 1
    apply (Nat.find_eq_iff _).mpr
    refine ⟨rfl, ?_⟩
    intro index earlier
    have same : index = 0 := by omega
    subst index
    intro impossible
    cases impossible
  · rename_i impossible
    exact False.elim (impossible ⟨1, rfl⟩)

theorem compiled_first :
    compiled ((activated contested).recall ()) ((activated contested).observe app ()) =
      FinDist.pure bindingAction := by
  have inconsistent : ¬ (runtime.prescribedReactivePolicy leaks () zeroPolicy).Consistent
      ((activated contested).recall ()) := contested_inconsistent
  rw [compiled, compileReactivePolicy, ReactiveApplication.Policy.recover_eq_recovery _ _ _ _
    inconsistent]
  have grant : ((activated contested).observe app ()).application.publicView.serviceGrant =
      some 0 := rfl
  have ready : ((activated contested).observe app ()).application.publicView.EventReady 0 := by
    decide
  have actor : graph.actor? 0 = some () := rfl
  rw [recoverReactivePolicy_apply]
  simp only [recoverReactiveResponse, grant, dite_true, ite_eq_left ready,
    dite_eq_left actor, EventGraph.normalizePolicy, zeroPolicy, Fin.cases_zero,
    reactiveRecoveryLaw_pure (graph := graph), FinDist.map_pure, FinDist.bind_const]
  change FinDist.pure (ReactiveApplication.Action.mk (app := app)
    ((reactiveFreshSlot ((activated contested).observe app ()).application).map _)) = _
  rw [recovery_slot]
  rfl

theorem granted_inconsistent (repair fresh : Bool) :
    ¬ (runtime.prescribedReactivePolicy leaks () zeroPolicy).Consistent
      ((activated (granted repair fresh)).recall ()) := by
  apply inconsistent_of_first
  apply List.prefix_iff_eq_take.mpr
  cases repair <;> cases fresh <;> rfl

theorem compiled_later (repair fresh : Bool) (possible : fresh = true → repair = true) :
    compiled ((activated (granted repair fresh)).recall ())
      ((activated (granted repair fresh)).observe app ()) = FinDist.pure (finalOpening fresh) := by
  rw [compiled, compileReactivePolicy, ReactiveApplication.Policy.recover_eq_recovery _ _ _ _
    (granted_inconsistent repair fresh)]
  have grant :
      ((activated (granted repair fresh)).observe app ()).application.publicView.serviceGrant =
        some 1 := rfl
  have publicState : ((activated (granted repair fresh)).observe app ()).application.publicView =
      (disclosed repair fresh).application.publicView := rfl
  have ready : ((activated (granted repair fresh)).observe app ()).application.publicView.EventReady
      1 := by
    rw [publicState]
    exact ((disclosed repair fresh).application.publicView_eventReady 1).mpr
      (disclosure_ready repair fresh possible)
  have actor : graph.actor? 1 = some () := rfl
  rw [recoverReactivePolicy_apply]
  simp only [recoverReactiveResponse, grant, dite_true, ite_eq_left ready,
    dite_eq_left actor, EventGraph.normalizePolicy, zeroPolicy_resolve,
    reactiveRecoveryLaw_pure (graph := graph), FinDist.map_pure, FinDist.bind_const]
  congr 1
  have state : (granted repair fresh).application =
      { boundState repair fresh with serviceGrant := some 1 } :=
    disclosed_state repair fresh possible
  change runtime.reactiveDecision leaks () 1 true
    ⟨(), (granted repair fresh).application.publicView,
      graph.playerObserve () (granted repair fresh).application.config,
      fun slot => (granted repair fresh).application.candidates.lookup ((), slot)⟩ = _
  rw [state]
  cases repair <;> cases fresh <;> first | contradiction | rfl

def earlyPolicy : app.Policy := fun history view =>
  if view.application.publicView.serviceGrant = some 0 then FinDist.pure earlyOpening
  else compiled history view

theorem earlyPolicy_first :
    earlyPolicy ((activated contested).recall ()) ((activated contested).observe app ()) =
      FinDist.pure earlyOpening := by
  have grant : ((activated contested).observe app ()).application.publicView.serviceGrant =
      some 0 := rfl
  simp only [earlyPolicy, grant, ↓reduceIte]

theorem earlyPolicy_later :
    earlyPolicy ((activated (granted false false)).recall ())
      ((activated (granted false false)).observe app ()) = FinDist.pure (finalOpening false) := by
  have different :
      ((activated (granted false false)).observe app ()).application.publicView.serviceGrant ≠
        some 0 := by decide
  rw [earlyPolicy, ite_eq_right different, compiled_later false false (by simp)]

end VegasTests.ReactiveEarlyOpening
