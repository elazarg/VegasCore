/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceGraph
import VegasTests.PendingStages
import VegasTests.PendingSource

/-! # Source-policy compilation regressions

A later decision copies an earlier public observation. The compiler preserves
their joint law, not just the set of possible source executions. Separate
regressions exercise arbitrary unilateral kernels and the two-player source
whose commitments are simultaneously ready.
-/

noncomputable section

namespace VegasTests.SourceGraph

open Vegas Vegas.EventGraph Vegas.ToEventGraph GameTheory GameTheory.Math.Probability
open PendingStages

def repeatPolicy (law : FinDist Value) : SourceBehavioralProfile core := by
  intro who Δ name ty guard site visible
  have hwho : who = 0 := Subsingleton.elim _ _
  subst who
  unfold core at site
  cases site with
  | here => exact law.map fun value => ⟨value, by cases value <;> rfl⟩
  | commit site =>
      cases site with
      | reveal site =>
          cases site with
          | here => exact FinDist.pure ⟨visible.get .here, by
              cases visible.get .here <;> rfl⟩
          | commit site => cases site with | reveal site => cases site

def repeatedOutcome (value : Value) : VEnv simpleExpr (sourceTerminalCtx core) :=
  (((VEnv.empty simpleExpr).cons value).cons value).cons value |>.cons value

theorem source_repeat_law (law : FinDist Value) :
    denoteSource core (repeatPolicy law) (VEnv.empty simpleExpr) =
      law.map repeatedOutcome := by
  simp only [core, denoteSource, repeatPolicy, VegasCore.commit.noConfusion,
    VegasCore.reveal.noConfusion, VegasCore.noConfusion, id_eq, FinDist.bind_map,
    SourceBehavioralProfile.afterCommit, SourceBehavioralProfile.afterReveal,
    FinDist.pure_bind]
  rw [FinDist.map_eq_bind]
  apply FinDist.bind_congr
  intro value _
  cases value <;> rfl

/-- The second commitment follows the first disclosed choice for any finite
first-choice law, including an explicit source decline. -/
theorem compiled_repeat_law (law : FinDist Value) :
    ((policyGame graph compiled.graphWF (compile_guardLive source.core source.legal)).play
      (source.sourceGraphSimulation.compileProfile (repeatPolicy law))).map
        (observeSourceOutcome source.core) =
      law.map (fun value => some (repeatedOutcome value)) := by
  have hlaw := source.sourceGraphSimulation.honest_law (repeatPolicy law)
  refine hlaw.trans ?_
  change (denoteSource core (repeatPolicy law) (VEnv.empty simpleExpr)).map some = _
  rw [source_repeat_law, FinDist.map_comp]
  rfl

/-- No graph replacement can create a source-outcome law unavailable to a
legal source replacement against the unchanged opposing player. -/
theorem two_player_deviation
    (profile : SourceBehavioralProfile PendingSource.core) (who : PendingSource.Player)
    (replacement : CommitPolicy PendingSource.graph who) :
    ((policyGame PendingSource.graph PendingSource.compiled.graphWF
      (compile_guardLive PendingSource.source.core PendingSource.source.legal)).play
      (Profile.update
        (PendingSource.source.sourceGraphSimulation.compileProfile profile)
        who replacement)).map (observeSourceOutcome PendingSource.source.core) =
      (denoteSource PendingSource.core
        (Profile.update (sig := sourceGameSignature PendingSource.core) profile who
          (backtranslateCommitPolicy PendingSource.source.core who replacement))
        (VEnv.empty simpleExpr)).map some :=
  runPolicyNodes_source_deviation PendingSource.source.core PendingSource.source.legal
    profile who replacement

/-- The sample is Boolean; the guarded commitment is nullable Boolean.
Its non-quitting value must match the public sample. -/
def sampledCore (law : RationalLaw Bool) : VegasCore PendingStages.Player simpleExpr [] :=
  .sample 0 (b := .bool) (.weighted law)
    (.commit 1 0 (b := .option .bool)
      (Expr.nullableCommitGuard (.eq (.var 1 .here) (.var 0 (.there .here))))
      (.reveal 2 0 1 .here (.ret [])))

def sampledSource (law : RationalLaw Bool) : WFProgram PendingStages.Player simpleExpr where
  core := {
    Γ := []
    prog := sampledCore law
    env := VEnv.empty simpleExpr
    wctx := by simp
    fresh := by simp [sampledCore, FreshBindings, Fresh] }
  accounted := CommitmentAccounting.ofRevealComplete (sampledCore law)
    (by simp [sampledCore, FreshBindings, Fresh]) [] (by simp)
    (by simp [sampledCore, RevealComplete])
  legal := by
    constructor
    · intro env
      exact ⟨declineValue .bool, evalExpr_nullableCommitGuard_declineValue _ _⟩
    · trivial

/-- The source certificate does not inherit the sealed backend's no-sample,
homogeneous-type, or unrestricted-guard limitations. -/
theorem sampled_guarded_law (law : RationalLaw Bool)
    (profile : SourceBehavioralProfile (sampledCore law)) :
    ((policyGame (compile (sampledSource law).core).graph
      (compile (sampledSource law).core).graphWF
      (compile_guardLive (sampledSource law).core (sampledSource law).legal)).play
        ((sampledSource law).sourceGraphSimulation.compileProfile profile)).map
      (observeSourceOutcome (sampledSource law).core) =
      (denoteSource (sampledCore law) profile (VEnv.empty simpleExpr)).map some :=
  (sampledSource law).sourceGraphSimulation.honest_law profile

end VegasTests.SourceGraph

/-- info: 'VegasTests.SourceGraph.compiled_repeat_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.SourceGraph.compiled_repeat_law

/-- info: 'VegasTests.SourceGraph.two_player_deviation' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.SourceGraph.two_player_deviation
