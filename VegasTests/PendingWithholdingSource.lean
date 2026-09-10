/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.PendingWithholding
import VegasTests.PendingSnapshots

/-! # Publication obstruction for informed withholding

The concrete withholding run is compared only against the publication carried
by the final public source binding. This rules out a publication-preserving
terminal-law comparison for this run and schedule; it does not rule out coarser
decoders or assert an equilibrium result.
-/

namespace VegasTests.PendingWithholdingSource

open Interaction Interaction.SealedProgram GameTheory GameTheory.Math.Probability
open VegasTests.PendingSource VegasTests.PendingExecution
open VegasTests.PendingWithholding VegasTests.PendingPolicies VegasTests.PendingSnapshots
open Interaction.MessageApplication

noncomputable section

def runtimePublication : List (Event PendingSource.Player Value) → Option Value
  | [] => none
  | .opened 3 value :: _ => some value
  | _ :: rest => runtimePublication rest

def sourcePublication
    (env : Vegas.VEnv Vegas.simpleExpr (Vegas.sourceTerminalCtx source.core.prog)) : Option Value :=
  some (env.get .here)

theorem withholding_runtime_publication :
    (law (some true)).map (fun execution =>
      runtimePublication execution.native.application.events) =
      FinDist.pure none := by
  rw [law_eq_final, FinDist.map_pure]
  rfl

/-- Every source terminal outcome has a final public binding, even when that
binding's value is itself `none`. Hence no source behavioral profile has the
same publication law as the concrete informed-withholding run. -/
theorem withholding_not_source_publication
    (sourceProfile : Vegas.SourceBehavioralProfile source.core.prog) :
    (law (some true)).map (fun execution =>
      runtimePublication execution.native.application.events) ≠
      ((Vegas.sourceGameForm source.core.prog source.core.env).play sourceProfile).map
        sourcePublication := by
  rw [withholding_runtime_publication]
  intro heq
  obtain ⟨env, henv⟩ :=
    ((Vegas.sourceGameForm source.core.prog source.core.env).play sourceProfile).support_nonempty
  have hpublication : sourcePublication env ∈
      (((Vegas.sourceGameForm source.core.prog source.core.env).play sourceProfile).map
        sourcePublication).support := by
    rw [FinDist.support_map]
    exact ⟨env, henv, rfl⟩
  rw [← heq] at hpublication
  have hnone := FinDist.mem_support_pure.mp hpublication
  simp [sourcePublication] at hnone

/-- Positive control at the same reached prefix and within the same remaining
invocation horizon: the canonical commit/open controller submits its
bound value rather than withholding after seeing player zero's true opening. -/
theorem canonical_playerOne_command :
    commitOpenPolicy program 1 1 3 (some false)
        ((s9 (some true)).principalHistory 1)
        (MessageApplication.State.observe Application (s9 (some true)).native 1) =
      FinDist.pure (.submit (.opening 3 (1, 1) (some false))) := by
  rfl

def canonical10 : Application.PolicyExecution :=
  playerSnapshot 1 (s9 (some true)) (.submit (.opening 3 (1, 1) (some false)))
    { (s9 (some true)).native with
      pool := ((s9 (some true)).native.pool.submit 1 (.opening 3 (1, 1) (some false))).2 }

def canonical11 : Application.PolicyExecution :=
  environmentSnapshot canonical10 (.include (1, 1))
    (Application.includePending canonical10.native (1, 1))

theorem canonical_controller_completes_same_horizon :
    canonical11.native.application.events =
      [.accepted 0 (0, 0), .accepted 1 (1, 1),
        .opened 2 (some true), .opened 3 (some false)] ∧
    canonical11.native.application.service.lookup (1, 1) = some (some false) := by
  exact ⟨rfl, rfl⟩

def canonicalProfile :
    Profile (MessageApplication.policySignature PendingSource.Player Application) :=
  Profile.update (profile (some true)) 1
    (commitOpenPolicy program 1 1 3 (some false))

def canonicalSuffixLaw : FinDist (Application.PolicyExecution) :=
  Application.runPolicies canonicalProfile environment
    [.player 1, .environment] (s9 (some true))

/-- The positive control uses the actual policy runner and the unchanged
environment policy: player one submits, then the environment performs its
fifth command and includes that opening. -/
theorem canonical_suffix_law : canonicalSuffixLaw = FinDist.pure canonical11 := by
  have hplayer : Application.invoke canonicalProfile environment (s9 (some true)) (.player 1) =
      FinDist.pure canonical10 := by
    apply invokePlayer_snapshot
    · simpa only [canonicalProfile, Profile.update_same] using canonical_playerOne_command
    · rfl
  have henvironment : Application.invoke canonicalProfile environment canonical10 .environment =
      FinDist.pure canonical11 := by
    apply invokeEnvironment_snapshot <;> rfl
  simp only [canonicalSuffixLaw, MessageApplication.runPolicies, hplayer, henvironment,
    FinDist.pure_bind]

end

end VegasTests.PendingWithholdingSource

/-- info: 'VegasTests.PendingWithholdingSource.withholding_not_source_publication' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.PendingWithholdingSource.withholding_not_source_publication
