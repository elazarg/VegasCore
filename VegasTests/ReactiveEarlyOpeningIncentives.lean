/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.ReactiveEarlyOpeningPolicy

/-! # Continuation incentives with uniform, at-most-once inclusion -/

noncomputable section

namespace VegasTests.ReactiveEarlyOpening

open GameTheory GameTheory.Protocol GameTheory.Math.Probability Interaction
open Vegas Vegas.EventGraphRuntime

theorem first_round (policy : app.Policy) :
    app.round scheduler (fun _ => policy) contested =
      (policy ((activated contested).recall ()) ((activated contested).observe app ())).map
        (fun action => (activated contested).respond app () action) := by
  change (FinDist.pure (.activate () : app.Command)).bind _ = _
  simp only [FinDist.pure_bind, ReactiveApplication.dispatch, activation,
    ReactiveApplication.Command.actor?, ReactiveApplication.resume, ReactiveApplication.invoke]

theorem compiled_first_round :
    app.round scheduler (fun _ => compiled) contested = FinDist.pure (afterResponse true) := by
  rw [first_round, compiled_first, FinDist.map_pure]
  rfl

theorem early_first_round :
    app.round scheduler (fun _ => earlyPolicy) contested = FinDist.pure (afterResponse false) := by
  rw [first_round, earlyPolicy_first, FinDist.map_pure]
  rfl

theorem binding_round (policy : app.Policy) (repair : Bool) :
    app.round scheduler (fun _ => policy) (afterResponse repair) =
      if repair then half (FinDist.pure (included true false))
        (FinDist.pure (included true true)) else FinDist.pure (included false false) := by
  have choice : scheduler (afterResponse repair).environmentRecall
      ((afterResponse repair).observeEnvironment app) =
        select 0 ((afterResponse repair).observeEnvironment app) := by cases repair <;> rfl
  rw [ReactiveApplication.round, choice, binding_selection]
  cases repair <;> simp only [Bool.false_eq_true, ↓reduceIte, half, FinDist.mix_bind,
    FinDist.pure_bind,
    ReactiveApplication.dispatch, ReactiveApplication.Execution.environmentStep,
    FinDist.map_pure, ReactiveApplication.Command.actor?, ReactiveApplication.resume]
  all_goals rfl

theorem grant_round (policy : app.Policy) (repair fresh : Bool) :
    app.round scheduler (fun _ => policy) (included repair fresh) =
      FinDist.pure (granted repair fresh) := by
  have choice : scheduler (included repair fresh).environmentRecall
      ((included repair fresh).observeEnvironment app) =
        FinDist.pure (.application (.grant 1)) := by cases repair <;> cases fresh <;> rfl
  rw [ReactiveApplication.round, choice, FinDist.pure_bind]
  simp only [ReactiveApplication.dispatch, ReactiveApplication.Execution.environmentStep,
    app, reactiveApplication, environmentStep, FinDist.map_pure, FinDist.pure_bind,
    ReactiveApplication.Command.actor?, ReactiveApplication.resume]
  rfl

theorem disclosure_round (policy : app.Policy) (repair fresh : Bool)
    (responds : policy ((activated (granted repair fresh)).recall ())
      ((activated (granted repair fresh)).observe app ()) = FinDist.pure (finalOpening fresh)) :
    app.round scheduler (fun _ => policy) (granted repair fresh) =
      FinDist.pure (disclosed repair fresh) := by
  have choice : scheduler (granted repair fresh).environmentRecall
      ((granted repair fresh).observeEnvironment app) = FinDist.pure (.activate ()) := by
    cases repair <;> cases fresh <;> rfl
  rw [ReactiveApplication.round, choice, FinDist.pure_bind]
  simp only [ReactiveApplication.dispatch, activation, FinDist.pure_bind,
    ReactiveApplication.Command.actor?, ReactiveApplication.resume, ReactiveApplication.invoke,
    responds, FinDist.map_pure]
  rfl

theorem repaired_publication_selection (fresh : Bool) :
    select 1 ((disclosed true fresh).observeEnvironment app) =
      half (FinDist.pure (.include ((), 1))) (FinDist.pure (.include ((), 3))) := by
  cases fresh <;>
    change ((MessageNetwork.chooseUniform {((), 1), ((), 3)}).map _).map _ = _
  all_goals
    rw [selection_pair _ _ (by decide)]
    simp only [half, FinDist.map_mix, FinDist.map_pure]
    rfl

theorem early_publication_selection :
    select 1 ((disclosed false false).observeEnvironment app) =
      third (FinDist.pure (.include ((), 1)))
        (half (FinDist.pure (.include ((), 2))) (FinDist.pure (.include ((), 3)))) := by
  change ((MessageNetwork.chooseUniform {((), 1), ((), 2), ((), 3)}).map _).map _ = _
  rw [MessageNetwork.chooseUniform_insert {((), 2), ((), 3)} (by decide) ((), 1) (by decide),
    selection_pair _ _ (by decide)]
  norm_num only [Finset.card_insert_of_notMem (show ((), 2) ∉ ({((), 3)} : Finset (MessageId Unit))
    by decide), Finset.card_singleton, Nat.cast_add, Nat.cast_one]
  simp only [half, third, FinDist.map_mix, FinDist.map_pure]
  norm_num
  rfl

theorem publication_choice (policy : app.Policy) (repair fresh : Bool) :
    app.round scheduler (fun _ => policy) (disclosed repair fresh) =
      (select 1 ((disclosed repair fresh).observeEnvironment app)).bind
        (fun command => app.dispatch (fun _ => policy) command (disclosed repair fresh)) := by
  cases repair <;> cases fresh <;> rfl

theorem repaired_publication_round (policy : app.Policy) (fresh : Bool) :
    app.round scheduler (fun _ => policy) (disclosed true fresh) =
      half (FinDist.pure (finished true fresh 1)) (FinDist.pure (finished true fresh 3)) := by
  rw [publication_choice, repaired_publication_selection]
  simp only [half, FinDist.mix_bind, FinDist.pure_bind, ReactiveApplication.dispatch,
    ReactiveApplication.Execution.environmentStep, FinDist.map_pure,
    ReactiveApplication.Command.actor?, ReactiveApplication.resume]
  rfl

theorem early_publication_round :
    app.round scheduler (fun _ => earlyPolicy) (disclosed false false) =
      third (FinDist.pure (finished false false 1))
        (half (FinDist.pure (finished false false 2)) (FinDist.pure (finished false false 3))) := by
  rw [publication_choice, early_publication_selection]
  simp only [half, third, FinDist.mix_bind, FinDist.pure_bind, ReactiveApplication.dispatch,
    ReactiveApplication.Execution.environmentStep, FinDist.map_pure,
    ReactiveApplication.Command.actor?, ReactiveApplication.resume]
  rfl

theorem compiled_rounds :
    app.runRounds scheduler (fun _ => compiled) 5 contested =
      half (half (FinDist.pure (finished true false 1)) (FinDist.pure (finished true false 3)))
        (half (FinDist.pure (finished true true 1)) (FinDist.pure (finished true true 3))) := by
  simp only [ReactiveApplication.runRounds, compiled_first_round, FinDist.pure_bind,
    binding_round, ↓reduceIte, half, FinDist.mix_bind, grant_round,
    disclosure_round compiled true false (compiled_later true false (by simp)),
    disclosure_round compiled true true (compiled_later true true (by simp)),
    repaired_publication_round, FinDist.bind_pure]

theorem early_rounds :
    app.runRounds scheduler (fun _ => earlyPolicy) 5 contested =
      third (FinDist.pure (finished false false 1))
        (half (FinDist.pure (finished false false 2)) (FinDist.pure (finished false false 3))) := by
  simp only [ReactiveApplication.runRounds, early_first_round, FinDist.pure_bind,
    binding_round, Bool.false_eq_true, ↓reduceIte, grant_round,
    disclosure_round earlyPolicy false false earlyPolicy_later, early_publication_round,
    FinDist.bind_pure]

end VegasTests.ReactiveEarlyOpening
