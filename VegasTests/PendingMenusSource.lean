/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.PendingMenusStrategies
import Vegas.Game.BehavioralSubgame

/-! # A common source SPE and the native pending-menu obstruction

One player binds an integer and discloses it. Binding zero and always opening
is optimal in every source continuation for both public utility tests. This
holds for either commitment admission: allowing forfeiture does not repair
the native service's competing-packet continuation.
-/

noncomputable section

namespace VegasTests.PendingMenus

open Vegas Vegas.SourceProgram GameTheory GameTheory.Protocol GameTheory.Math.Probability

private def guard : SourceGuard simpleExpr ([] : SourceCtx Unit simpleExpr) () 0 .int where
  schema := []
  schemaNames := by decide
  subjectFresh := by decide
  code := .constBool true
  reads := fun impossible => nomatch impossible

def sourceProgram : SourceProgram Unit simpleExpr [] ∅ :=
  .commit 0 () (by decide) guard <|
  .reveal 1 () 0 (by decide) .here (by decide) <|
  .ret []

def sourceInitial : Config Unit simpleExpr [] :=
  ⟨Env.empty _, [], Revelations.initial [], fun _ => []⟩

def sourcePolicy (who : Unit) : BehavioralPolicy who sourceProgram :=
  (fun _ _ => FinDist.pure (.success 0), (fun _ _ => FinDist.pure true, PUnit.unit))

theorem source_admitted (admission : CommitmentInterface sourceProgram) (who : Unit) :
    (sourcePolicy who).Admitted sourceProgram admission := by
  refine ⟨?_, trivial⟩
  intro _ _ choice reached
  have same := FinDist.mem_support_pure.mp reached
  subst choice
  trivial

def sourceProfile (admission : CommitmentInterface sourceProgram) :
    Profile (admittedBehavioralSignature sourceProgram admission) :=
  fun who => ⟨sourcePolicy who, source_admitted admission who⟩

def sourceUtility (preferOne : Bool) (state : Vegas.State simpleExpr sourceProgram.terminalCtx)
    (_who : Unit) : ℝ := publicUtility preferOne (some (state.get .here))

private theorem utility_nonneg (preferOne : Bool) (result : PublicationResult Int) :
    0 ≤ publicUtility preferOne (some result) := by
  cases result with
  | failure => norm_num [publicUtility]
  | success value =>
      simp only [publicUtility]
      split_ifs <;> norm_num

private theorem utility_le_three (preferOne : Bool) (result : PublicationResult Int) :
    publicUtility preferOne (some result) ≤ 3 := by
  cases result with
  | failure => norm_num [publicUtility]
  | success value =>
      simp only [publicUtility]
      split_ifs <;> norm_num

private theorem empty_registry (config : Config Unit simpleExpr []) : config.registry = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro obligation _
  exact nomatch obligation.source

/-- Exact public meaning of the source program, including both failure choices. -/
theorem source_publication (config : Config Unit simpleExpr [])
    (choice : PublicationResult Int) (disclose : Bool) :
    (revealSuccessor 1 .here (commitSuccessor 0 guard config choice) disclose).state.get .here =
      if disclose then choice else .failure := by
  simp only [revealSuccessor, commitSuccessor, empty_registry config]
  cases disclose <;> cases choice <;> rfl

/-- The native example's two-event graph has exactly the source publication
kernel, for every binding and disclosure, including forfeiture and withholding. -/
theorem source_graph_publication (choice : PublicationResult Int) (disclose : Bool) :
    let bound := (EventGraph.Config.initial (graph := graph) input).complete 0
      (by decide) choice choice
    (graph.nodes 1).eval? disclose bound.store =
      some (FinDist.pure
        ((revealSuccessor 1 .here (commitSuccessor 0 guard sourceInitial choice)
          disclose).state.get .here)) := by
  rw [source_publication]
  change (EventGraph.EventCode.resolve _ _ binding []).eval? disclose _ = _
  cases disclose <;> cases choice <;>
    simp [EventGraph.EventCode.eval?, EventGraph.EventCode.resolveOutput?,
      EventGraph.FieldRef.get?, EventGraph.Config.store,
      EventGraph.Config.complete_output_same, EventGraph.GuardCheck.allAccepted?]

private theorem honest_commit_value (preferOne : Bool) (config : Config Unit simpleExpr []) :
    (ProtocolState.continuationLaw sourceProgram sourcePolicy (Sum.inl config)).expect
      (sourceUtility preferOne · ()) = 3 := by
  simp only [sourceProgram, ProtocolState.continuationLaw, Sum.elim_inl, runFrom_commit,
    commitKernel, sourcePolicy, FinDist.pure_bind, runFrom_reveal, afterCommit, revealKernel]
  change (FinDist.pure (revealSuccessor 1 .here
    (commitSuccessor 0 guard config (.success 0)) true).state).expect _ = _
  rw [FinDist.expect_pure]
  change publicUtility preferOne (some ((revealSuccessor 1 .here
    (commitSuccessor 0 guard config (.success 0)) true).state.get .here)) = _
  rw [source_publication]
  norm_num [publicUtility]

private theorem withholding_result
    (config : Config Unit simpleExpr [(0, .commitment () .int)]) :
    (revealSuccessor 1 .here config false).state.get .here = PublicationResult.failure := by
  simp only [revealSuccessor, Bool.false_eq_true, ↓reduceIte, Env.get, Env.cons]
  split <;> rfl

/-- Even arbitrary source configurations satisfy the local optimality test:
opening weakly dominates withholding, and a fresh zero earns the global maximum. -/
theorem source_continuation_optimal (preferOne : Bool)
    (replacement : BehavioralProfile sourceProgram) (state : ProtocolState sourceProgram) :
    (ProtocolState.continuationLaw sourceProgram replacement state).expect
        (sourceUtility preferOne · ()) ≤
      (ProtocolState.continuationLaw sourceProgram sourcePolicy state).expect
        (sourceUtility preferOne · ()) := by
  cases state with
  | inl config =>
      rw [honest_commit_value]
      exact FinDist.expect_le_of_forall _ _ _ (fun final _ =>
        utility_le_three preferOne (final.get .here))
  | inr state =>
      cases state with
      | inr config => exact le_rfl
      | inl config =>
          change (((replacement ()).2.1 rfl (config.view ())).bind (fun disclose =>
            FinDist.pure (revealSuccessor 1 .here config disclose).state)).expect _ ≤
            ((FinDist.pure true).bind (fun disclose =>
              FinDist.pure (revealSuccessor 1 .here config disclose).state)).expect _
          rw [FinDist.pure_bind, FinDist.expect_pure, FinDist.expect_bind]
          apply FinDist.expect_le_of_forall
          intro disclose _
          rw [FinDist.expect_pure]
          cases disclose with
          | true => exact le_rfl
          | false =>
              change publicUtility preferOne (some
                ((revealSuccessor 1 .here config false).state.get .here)) ≤ _
              rw [withholding_result]
              exact utility_nonneg preferOne _

abbrev sourceModel (admission : CommitmentInterface sourceProgram) :=
  informationModel sourceProgram admission sourceInitial

def sourceProtocolProfile (admission : CommitmentInterface sourceProgram) :
    Profile (sourceModel admission).behavioralSignature :=
  Profile.map (fun who => behavioralPolicyEquiv sourceProgram admission sourceInitial who)
    (sourceProfile admission)

/-- The same source profile is a behavioral SPE for both public utilities,
under either value-only or forfeiture-admitting commitment semantics. -/
theorem source_spe (admission : CommitmentInterface sourceProgram) (preferOne : Bool) :
    (sourceModel admission).IsBehavioralSubgamePerfect
      (protocol_singleMover sourceProgram admission sourceInitial)
      (protocol_bounded sourceProgram admission sourceInitial)
      (sourceProtocolProfile admission)
      (protocolUtility sourceProgram admission sourceInitial (sourceUtility preferOne)) := by
  rw [sourceProtocolProfile, protocol_isBehavioralSubgamePerfect_iff]
  intro history _ who alternative
  cases who
  exact source_continuation_optimal preferOne _ history.state

/-- No utility-independent translation of this source game into the specified
native service preserves behavioral SPE for all public outcome utilities.
The statement allows arbitrary whole-profile translators, a larger class than
playerwise compilers. It is not an impossibility for every runtime. -/
theorem no_utility_independent_spe_compiler (admission : CommitmentInterface sourceProgram) :
    ¬ ∃ compile : Profile (sourceModel admission).behavioralSignature →
        Profile nativeModel.behavioralSignature,
      ∀ preferOne,
        (sourceModel admission).IsBehavioralSubgamePerfect
          (protocol_singleMover sourceProgram admission sourceInitial)
          (protocol_bounded sourceProgram admission sourceInitial)
          (sourceProtocolProfile admission)
          (protocolUtility sourceProgram admission sourceInitial (sourceUtility preferOne)) →
        nativeModel.IsBehavioralSubgamePerfect
          (runtime.native_singleMover (FinDist.pure input) [] 1 wire ordering)
          (runtime.native_bounded (FinDist.pure input) [] 1 wire ordering)
          (compile (sourceProtocolProfile admission)) (nativePayoff preferOne) := by
  rintro ⟨compile, preserves⟩
  exact no_common_native_spe ⟨compile (sourceProtocolProfile admission),
    preserves true (source_spe admission true), preserves false (source_spe admission false)⟩

end VegasTests.PendingMenus
