/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.ReactiveEarlyOpeningIncentives
import Vegas.Source.Honest

/-! # Readiness tokens remove the early-opening deviation

The source binds zero and opens. At a proper native root an earlier
withholding packet is pending, and the owner may transmit an opening before
the disclosure is ready. Every selection is uniform over distinct unpublished
envelopes for one event; activation times are fixed.

Packets carry the readiness token of their event, attached at emission, and
the contract rejects a packet without one. Both packets sent before the
disclosure became ready are therefore rejected whenever they are selected,
and the early opening is strictly worse than the compiler's recovery. An
unfinished disclosure has the same payoff as a withheld one.
-/

noncomputable section

namespace Vegas.Examples.ReactiveEarlyOpening

open GameTheory GameTheory.Protocol GameTheory.Math.Probability Interaction
open Vegas Vegas.EventGraphRuntime Vegas.SourceProgram

def result (state : app.ProtocolState) : Option (PublicationResult Int) :=
  state.bind fun control => control.execution.application.config.outputs 1

def run (policy : app.Policy) : PMF arena.History :=
  model.runSingleMoverBehavioralFrom (app.singleMover (PMF.pure initialState) 6 scheduler)
    (fun _ => app.encodePolicy policy) 13 (secondHistory first second)

theorem run_state (policy : app.Policy) : (run policy).map ExecutionProtocol.History.state =
    (app.runRounds scheduler (fun _ => policy) 4 contested).map app.finished := by
  rw [run, app.run_map_state]
  change (fun law : PMF app.ProtocolState => law.bind
    (app.controlStep (PMF.pure initialState) 6 scheduler (fun _ => policy)))^[13]
      (PMF.pure (some ⟨4, none, contested⟩)) = _
  simpa only [ReactiveApplication.finish, ReactiveApplication.resume, PMF.pure_bind] using
    app.iterate_eq_finish (PMF.pure initialState) 6 scheduler (fun _ => policy)
      13 (some ⟨4, none, contested⟩) (by change 2 * 4 + 0 ≤ 13; omega)

theorem run_value (policy : app.Policy) :
    expect (run policy) (fun final => PendingMenus.publicUtility true (result final.state)) =
      expect (app.runRounds scheduler (fun _ => policy) 4 contested)
        (fun final => PendingMenus.publicUtility true (final.application.config.outputs 1)) := by
  have equal := congrArg (fun law : PMF app.ProtocolState => expect law
    (fun state => PendingMenus.publicUtility true (result state))) (run_state policy)
  simpa only [expect_map, Function.comp_def, result, ReactiveApplication.finished,
    Option.bind_some] using equal

theorem run_publication (policy : app.Policy) :
    (run policy).map (fun final => result final.state) =
      (app.runRounds scheduler (fun _ => policy) 4 contested).map
        (fun final => final.application.config.outputs 1) := by
  have equal := congrArg (fun law : PMF app.ProtocolState => law.map result)
    (run_state policy)
  simpa only [PMF.map_comp, Function.comp_def, result, ReactiveApplication.finished,
    Option.bind_some]
    using equal

theorem compiled_publication :
    (run compiled).map (fun final => result final.state) =
      half (half (PMF.pure none) (PMF.pure (some (.success 1))))
        (half (PMF.pure none) (PMF.pure (some (.success 0)))) := by
  rw [run_publication, compiled_rounds]
  simp only [half, mix_map, PMF.pure_map,
    finished_withholding true false (by simp), finished_withholding true true (by simp),
    repaired_opening, Bool.false_eq_true, ↓reduceIte]

theorem early_publication :
    (run earlyPolicy).map (fun final => result final.state) =
      third (PMF.pure none) (half (PMF.pure none) (PMF.pure (some (.success 1)))) := by
  rw [run_publication, early_rounds]
  simp only [half, third, mix_map, PMF.pure_map,
    early_withholding, early_opening, later_opening]

theorem compiled_value :
    expect (run compiled) (fun final => PendingMenus.publicUtility true (result final.state)) =
      5 / 4 := by
  rw [run_value, compiled_rounds]
  simp only [half, expect_mix, payoffIntegrable_mix, payoffIntegrable_pure, expect_pure,
    finished_withholding true false (by simp), finished_withholding true true (by simp),
    repaired_opening]
  norm_num [PendingMenus.publicUtility]

theorem early_value :
    expect (run earlyPolicy) (fun final => PendingMenus.publicUtility true (result final.state)) =
      2 / 3 := by
  rw [run_value, early_rounds]
  simp only [half, third, expect_mix, payoffIntegrable_mix, payoffIntegrable_pure,
    expect_pure,
    early_withholding, early_opening, later_opening]
  norm_num [PendingMenus.publicUtility]

/-- The early opening, whose packets are rejected for lack of a readiness
token, is strictly worse than the compiler's recovery at the same root. -/
theorem early_opening_unprofitable :
    expect (run earlyPolicy) (fun final => PendingMenus.publicUtility true (result final.state)) <
      expect (run compiled) (fun final =>
        PendingMenus.publicUtility true (result final.state)) := by
  rw [early_value, compiled_value]
  norm_num

theorem source_honest : Honest PendingMenus.sourceProgram (PendingMenus.sourcePolicy ()) := by
  exact ⟨⟨fun _ _ => by simp [PendingMenus.sourcePolicy], trivial⟩,
    ⟨fun _ _ => by simp [PendingMenus.sourcePolicy], trivial⟩⟩

/-- The source profile is honest and SPE for either commitment interface, and
the early-opening deviation no longer improves on the actual graph-policy
recovery compiler: the readiness token makes its premature packets inert. The
source/graph publication semantics are identified by
`PendingMenus.source_graph_publication`. -/
theorem honest_source_early_opening_blocked
    (admission : CommitmentInterface PendingMenus.sourceProgram) :
    Honest PendingMenus.sourceProgram (PendingMenus.sourcePolicy ()) ∧
      (PendingMenus.sourceModel admission).IsSingleMoverBehavioralSubgamePerfect
        (protocol_singleMover PendingMenus.sourceProgram admission PendingMenus.sourceInitial)
        (protocol_bounded PendingMenus.sourceProgram admission PendingMenus.sourceInitial)
        (PendingMenus.sourceProtocolProfile admission)
        (protocolUtility PendingMenus.sourceProgram admission PendingMenus.sourceInitial
          (PendingMenus.sourceUtility true)) ∧
      expect (run earlyPolicy) (fun final => PendingMenus.publicUtility true (result final.state)) <
        expect (run compiled) (fun final =>
          PendingMenus.publicUtility true (result final.state)) :=
  ⟨source_honest, PendingMenus.source_spe admission true, early_opening_unprofitable⟩

theorem scheduler_atMostOnce : app.AtMostOnce scheduler := by
  intro history view id supported
  unfold scheduler at supported
  split at supported
  all_goals first
    | cases (PMF.mem_support_pure_iff _ _).mp supported
    | obtain ⟨requested, _, equal⟩ := PMF.support_map .. ▸ supported
      exact app.atMostOnceCommand_fresh view requested id equal

end Vegas.Examples.ReactiveEarlyOpening
