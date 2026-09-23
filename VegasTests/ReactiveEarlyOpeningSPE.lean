/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.ReactiveEarlyOpeningIncentives
import Vegas.Source.Honest

/-! # The honest recovery compiler need not preserve SPE under uniform inclusion

The source binds zero and opens. At a proper native root, transmitting an
opening early strictly improves on the actual compiler's recovery. Every
selection is uniform over distinct unpublished envelopes for one event;
activation times are fixed. This refutes this compiler under this service,
not the existence of all possible SPE-preserving implementations.
-/

noncomputable section

namespace VegasTests.ReactiveEarlyOpening

open GameTheory GameTheory.Protocol GameTheory.Math.Probability Interaction
open Vegas Vegas.EventGraphRuntime Vegas.SourceProgram

def result (state : app.ProtocolState) : Option (PublicationResult Int) :=
  state.bind fun control => control.execution.application.config.outputs 1

def run (policy : app.Policy) : FinDist arena.History :=
  model.runSingleMoverBehavioralFrom (app.singleMover (FinDist.pure initialState) 7 scheduler)
    (fun _ => app.encodePolicy policy) 15 (secondHistory first second)

theorem run_state (policy : app.Policy) : (run policy).map ExecutionProtocol.History.state =
    (app.runRounds scheduler (fun _ => policy) 5 contested).map app.finished := by
  rw [run, app.run_map_state]
  change (fun law : FinDist app.ProtocolState => law.bind
    (app.controlStep (FinDist.pure initialState) 7 scheduler (fun _ => policy)))^[15]
      (FinDist.pure (some ⟨5, none, contested⟩)) = _
  simpa only [ReactiveApplication.finish, ReactiveApplication.resume, FinDist.pure_bind] using
    app.iterate_eq_finish (FinDist.pure initialState) 7 scheduler (fun _ => policy)
      15 (some ⟨5, none, contested⟩) (by change 2 * 5 + 0 ≤ 15; omega)

theorem run_value (policy : app.Policy) :
    (run policy).expect (fun final => PendingMenus.publicUtility true (result final.state)) =
      (app.runRounds scheduler (fun _ => policy) 5 contested).expect
        (fun final => PendingMenus.publicUtility true (final.application.config.outputs 1)) := by
  have equal := congrArg (fun law : FinDist app.ProtocolState => law.expect
    (fun state => PendingMenus.publicUtility true (result state))) (run_state policy)
  simpa only [FinDist.expect_map, result, ReactiveApplication.finished, Option.bind_some]
    using equal

theorem run_publication (policy : app.Policy) :
    (run policy).map (fun final => result final.state) =
      (app.runRounds scheduler (fun _ => policy) 5 contested).map
        (fun final => final.application.config.outputs 1) := by
  have equal := congrArg (fun law : FinDist app.ProtocolState => law.map result)
    (run_state policy)
  simpa only [FinDist.map_comp, Function.comp_def, result, ReactiveApplication.finished,
    Option.bind_some]
    using equal

theorem compiled_publication :
    (run compiled).map (fun final => result final.state) =
      half (half (FinDist.pure (some .failure)) (FinDist.pure (some (.success 1))))
        (half (FinDist.pure (some .failure)) (FinDist.pure (some (.success 0)))) := by
  rw [run_publication, compiled_rounds]
  simp only [half, FinDist.map_mix, FinDist.map_pure,
    finished_withholding true false (by simp), finished_withholding true true (by simp),
    repaired_opening, Bool.false_eq_true, ↓reduceIte]

theorem early_publication :
    (run earlyPolicy).map (fun final => result final.state) =
      third (FinDist.pure (some .failure)) (FinDist.pure (some (.success 1))) := by
  rw [run_publication, early_rounds]
  simp only [half, third, FinDist.map_mix, FinDist.map_pure,
    early_withholding, early_opening, later_opening, FinDist.mix_self]

/-- Both compared continuations publish a result on every branch. The
counterexample does not assign a special payoff to an unfinished execution. -/
theorem compared_continuations_publish (policy : app.Policy)
    (compared : policy = compiled ∨ policy = earlyPolicy)
    (final : arena.History) (supported : final ∈ (run policy).support) :
    (result final.state).isSome = true := by
  have observed : result final.state ∈ ((run policy).map (fun last => result last.state)).support :=
    FinDist.support_map .. ▸ ⟨final, supported, rfl⟩
  rcases compared with rfl | rfl
  · rw [compiled_publication] at observed
    simp only [half, FinDist.mem_support_mix_iff _ _ _ (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 : ℝ) / 2 < 1)] at observed
    rcases observed with (observed | observed) | (observed | observed) <;>
      rw [FinDist.mem_support_pure.mp observed] <;> rfl
  · rw [early_publication] at observed
    simp only [third, FinDist.mem_support_mix_iff _ _ _ (by norm_num : (0 : ℝ) < 1 / 3)
      (by norm_num : (1 : ℝ) / 3 < 1)] at observed
    rcases observed with observed | observed <;>
      rw [FinDist.mem_support_pure.mp observed] <;> rfl

theorem compiled_value :
    (run compiled).expect (fun final => PendingMenus.publicUtility true (result final.state)) =
      5 / 4 := by
  rw [run_value, compiled_rounds]
  simp only [half, FinDist.expect_mix, FinDist.expect_pure,
    finished_withholding true false (by simp), finished_withholding true true (by simp),
    repaired_opening]
  norm_num [PendingMenus.publicUtility]

theorem early_value :
    (run earlyPolicy).expect (fun final => PendingMenus.publicUtility true (result final.state)) =
      4 / 3 := by
  rw [run_value, early_rounds]
  simp only [half, third, FinDist.expect_mix, FinDist.expect_pure,
    early_withholding, early_opening, later_opening]
  norm_num [PendingMenus.publicUtility]

def payoff (final : arena.History) (_who : Unit) : ℝ :=
  PendingMenus.publicUtility true (result final.state)

theorem compiled_not_spe :
    ¬ model.IsBehavioralSubgamePerfect (app.singleMover (FinDist.pure initialState) 7 scheduler)
      (app.bounded (FinDist.pure initialState) 7 scheduler)
      (fun _ => app.encodePolicy compiled) payoff := by
  intro perfect
  rw [InformationModel.isBehavioralSubgamePerfect_iff] at perfect
  have improves := perfect (secondHistory first second) contested_isSubgameRoot ()
    (app.encodePolicy earlyPolicy)
  have updated : Profile.update (sig := model.behavioralSignature)
      (fun _ => app.encodePolicy compiled : Profile model.behavioralSignature) ()
      (app.encodePolicy earlyPolicy) =
        (fun _ => app.encodePolicy earlyPolicy : Profile model.behavioralSignature) := by
    funext who
    cases who
    simp [Profile.update]
  rw [updated] at improves
  change (run earlyPolicy).expect (fun final => PendingMenus.publicUtility true
    (result final.state)) ≤ (run compiled).expect (fun final => PendingMenus.publicUtility true
      (result final.state)) at improves
  rw [early_value, compiled_value] at improves
  norm_num at improves

theorem source_honest : Honest PendingMenus.sourceProgram (PendingMenus.sourcePolicy ()) := by
  exact ⟨⟨fun _ _ => by simp [PendingMenus.sourcePolicy], trivial⟩,
    ⟨fun _ _ => by simp [PendingMenus.sourcePolicy], trivial⟩⟩

/-- The source profile is honest and SPE for either commitment interface;
the actual graph-policy recovery compiler is not native SPE. The source/graph
publication semantics are identified by `PendingMenus.source_graph_publication`. -/
theorem honest_source_spe_native_failure
    (admission : CommitmentInterface PendingMenus.sourceProgram) :
    Honest PendingMenus.sourceProgram (PendingMenus.sourcePolicy ()) ∧
      (PendingMenus.sourceModel admission).IsBehavioralSubgamePerfect
        (protocol_singleMover PendingMenus.sourceProgram admission PendingMenus.sourceInitial)
        (protocol_bounded PendingMenus.sourceProgram admission PendingMenus.sourceInitial)
        (PendingMenus.sourceProtocolProfile admission)
        (protocolUtility PendingMenus.sourceProgram admission PendingMenus.sourceInitial
          (PendingMenus.sourceUtility true)) ∧
      ¬ model.IsBehavioralSubgamePerfect (app.singleMover (FinDist.pure initialState) 7 scheduler)
        (app.bounded (FinDist.pure initialState) 7 scheduler)
        (fun _ => app.encodePolicy compiled) payoff :=
  ⟨source_honest, PendingMenus.source_spe admission true, compiled_not_spe⟩

theorem scheduler_atMostOnce : app.AtMostOnce scheduler := by
  intro history view id supported
  unfold scheduler at supported
  split at supported
  all_goals first
    | cases FinDist.mem_support_pure.mp supported
    | obtain ⟨requested, _, equal⟩ := FinDist.support_map .. ▸ supported
      exact app.atMostOnceCommand_fresh view requested id equal

end VegasTests.ReactiveEarlyOpening
