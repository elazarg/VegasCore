/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.SealedResolutionReservations
import Vegas.Game.SealedRounds
import VegasTests.SealedPolicy

/-! # Concrete strategic round-model regression

The checked four-node pending-stage source is run for sixty rounds with the
second round of each two-round period reserved for inclusion.  The utilities
below intentionally test the abstract utility-simulation mechanism: they are
not asserted to be a settlement interpretation of the written source.
-/

noncomputable section

namespace VegasTests.SealedRounds

open Vegas Vegas.EventGraph Vegas.ToEventGraph Vegas.SealedCompilation
open Interaction Interaction.MessageApplication Interaction.SealedResolution
open GameTheory GameTheory.Math.Probability
open PendingStages

private abbrev compilation := SealedPolicy.compilation
private abbrev runtime := supported.resolvingRuntime none 14
private abbrev app := runtime.messageApplication

private def model (base : app.WirePolicy) : RoundModel compilation none 14 where
  principals := [0]
  serviceSlots := 2
  total := 60
  wire := app.reserveInclusion (periodicFinalReservation 2 2) base
  budget := by decide

private def timely (base : app.WirePolicy) : (model base).Timely where
  reserved := periodicFinalReservation 2 2
  service := app.reserveInclusion_service _ base
  period := 2
  positive := by decide
  capacity := fun block => periodicFinalReservation_capacity [0] 2 2 block
    (by decide) (by decide)
  roster := by
    intro who
    fin_cases who
    simp [model]
  windowBound := by decide
  wholePeriods := ⟨30, rfl⟩

private def sourceUtility
    (_ : VEnv simpleExpr (sourceTerminalCtx core)) (_ : PendingStages.Player) : ℝ := 1

/-- Timeout-free completion receives one. An owner-attributable timeout
receives zero; the remaining unreachable/irrelevant cases also receive one.
This is only a regression utility for the abstract strategic theorem. -/
private noncomputable def nativeUtility (base : app.WirePolicy)
    (next : (model base).game.sig.Outcome) (who : PendingStages.Player) : ℝ := by
  classical
  exact if (model base).OwnTimeout who next then 0 else 1

private def floor (_ : PendingStages.Player) : ℝ := 1

private theorem normalUtilityAgreement (base : app.WirePolicy) :
    (model base).NormalUtilityAgreement sourceUtility (nativeUtility base) := by
  intro cfg next hterminal _hinvariant _hcomplete hclear _hdecode who
  have hnotOwn : ¬(model base).OwnTimeout who next := by
    intro hown
    obtain ⟨node, htimeout, _⟩ := hown
    rw [hclear] at htimeout
    simp at htimeout
  rw [observeSourceOutcome_of_terminal source.core cfg hterminal]
  simp [nativeUtility, sourceUtility, hnotOwn]

private theorem sourceFloor (outcome : VEnv simpleExpr (sourceTerminalCtx core))
    (who : PendingStages.Player) : floor who ≤ sourceUtility outcome who := by
  simp [floor, sourceUtility]

private theorem timeoutBound (base : app.WirePolicy)
    (next : (model base).game.sig.Outcome)
    (_hcomplete : runtime.complete next.native.application.visible = true)
    (who : PendingStages.Player) (hown : (model base).OwnTimeout who next) :
    nativeUtility base next who ≤ floor who := by
  simp [nativeUtility, floor, hown]

/-- The concrete checked source instantiates the exact source/native
equilibrium equivalence for every adaptive unreserved wire policy. -/
theorem concrete_isεNash_iff (base : app.WirePolicy) (ε : ℝ)
    (profile : SourceBehavioralProfile core) :
    IsεNash (model base).game (nativeUtility base) ε
      (fun who => compilation.compileResolvingPolicy none 14 who (profile who)) ↔
    IsεNash (sourceGameForm core source.core.env) sourceUtility ε profile :=
  (model base).isεNash_iff (timely base) sourceUtility (nativeUtility base)
    (normalUtilityAgreement base) floor sourceFloor (timeoutBound base) ε profile

/-- For nonnegative approximation error, the compiled profile is an actual
equilibrium witness. No native Nash premise is assumed: `IsεNash` itself
quantifies over every unrestricted native unilateral replacement. -/
theorem compiled_profile_isεNash (base : app.WirePolicy) (ε : ℝ) (hε : 0 ≤ ε)
    (profile : SourceBehavioralProfile core) :
    IsεNash (model base).game (nativeUtility base) ε
      (fun who => compilation.compileResolvingPolicy none 14 who (profile who)) := by
  apply (concrete_isεNash_iff base ε profile).2
  rw [GameTheory.isεNash_iff]
  intro who replacement
  simp only [GameTheory.expectedUtility, sourceUtility, FinDist.expect_const]
  linarith

end VegasTests.SealedRounds

/-- info: 'VegasTests.SealedRounds.compiled_profile_isεNash' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.SealedRounds.compiled_profile_isεNash
