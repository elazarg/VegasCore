/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedSourceCoverage
import Vegas.Compile.WindowedBindingLaw
import Vegas.Compile.BindingTimeoutCompilation
import Vegas.Compile.PublicChoiceResolution
import VegasTests.GeneratedApplicationPolicy
import VegasTests.ApplicationBindingOrigins
import VegasTests.GeneratedApplicationSourceLaw

/-! # Complete source coverage with arbitrary raw replacement policies

The checked persistent-disclosure program exercises binding, public choice,
chance, conditional publication, and copied conditional publication. The
timeouts below compile explicit legal source expressions. Neither the whole
source profile nor the replacement player's randomized command policy is
specialized to a scripted execution.
-/

noncomputable section

namespace VegasTests.WindowedSourceCoverage

open Vegas Vegas.EventGraph Vegas.ToEventGraph Interaction
  Interaction.MessageApplication GameTheory.Math.Probability
open VegasTests.PersistentDisclosure VegasTests.GeneratedPersistentDisclosure

def bindingFallback : SourceDecisionSite.PublicFallback GeneratedBindingPolicy.site where
  expr := .constBool false
  legal _ := rfl

def markerFallback :
    SourceDecisionSite.PublicFallback GeneratedApplicationPolicy.markerSite.decision where
  expr := .constBool false
  legal _ := rfl

def responseSite : PublicChoiceSite (P := TestPlayer) (L := simpleExpr)
    (.commit 6 (b := .bool) 1 (.constBool true) (.reveal 7 1 6 .here secondCore)) :=
  PublicChoiceSite.atHead (P := TestPlayer) (L := simpleExpr)
    (Γ := ResponseContext) (ty := .bool) 6 7 1 (.constBool true) secondCore

def responseFallback : SourceDecisionSite.PublicFallback responseSite.decision where
  expr := .constBool false
  legal _ := rfl

def bindingSelector (code : BindingCode TestPlayer simpleExpr) :
    Option (PublicFallbackCode simpleExpr code.ty) :=
  bindingFallback.selectBindingTimeout source.fresh compilerInitial 10 code

def choiceSelector (code : PublicChoiceCode TestPlayer simpleExpr) :
    Option (PublicFallbackCode simpleExpr code.guard.ty) :=
  let marker := GeneratedApplicationPolicy.markerSite.select markerFallback
    source.fresh.2 GeneratedApplicationPolicy.markerBuild 10 code
  responseSite.select responseFallback source.fresh.2.2.2.2.2.2 beforeResponse 10
    { code with timeout := marker }

/-- The actual selectors, not an assumed completion oracle, discharge every
source-fallback obligation of this mixed-feature generated program. -/
theorem block_fallbacks : applicationPlan.BlockFallbacks bindingSelector choiceSelector := by
  refine ⟨⟨bindingFallback, 10, rfl⟩, ⟨⟨markerFallback, 10, rfl⟩,
    ⟨⟨responseFallback, 10, rfl⟩, trivial⟩⟩⟩

def runtime : WindowedApplication TestPlayer simpleExpr :=
  applicationPlan.windowed (fun _ => 10) bindingSelector choiceSelector (fun _ => 10)

def initial : runtime.application.PolicyExecution :=
  applicationPlan.windowedInitialExecution (fun _ => 10) bindingSelector choiceSelector
    (fun _ => 10)

def players (profile : SourceBehavioralProfile source.prog)
    (replacement : runtime.application.PlayerPolicy) :
    TestPlayer → runtime.application.PlayerPolicy :=
  applicationPlan.windowedPlayers profile (fun _ => 10) bindingSelector choiceSelector
    (fun _ => 10) 0 replacement

/-- Every supported complete generated execution, under an arbitrary possibly
randomized raw deviation, terminates and has an actual sequential source run.
This is not a deviation-law or equilibrium-preservation theorem. -/
theorem complete_source_execution
    (profile : SourceBehavioralProfile source.prog)
    (replacement : runtime.application.PlayerPolicy)
    (final : runtime.application.PolicyExecution)
    (hfinal : final ∈ (runtime.application.runPolicies (players profile replacement)
      (runtime.blockEnvironment [0, 1])
      (List.replicate 6 (WindowedApplication.blockInvocations [0, 1])).flatten initial).support) :
    (∃ terminal : SourceConfig TestPlayer simpleExpr,
      SmallStep.Star ⟨source.Γ, source.env, source.prog⟩ terminal ∧ terminal.IsTerminal) ∧
      final.native.application.base.memory.finished 10 = true := by
  have checkpoint := ApplicationPlan.WindowedCheckpoint.initial
    DisclosureAccounting.persistentChecked applicationPlan profile (fun _ => 10)
    bindingSelector choiceSelector (fun _ => 10) [0, 1] 0 replacement
  exact ApplicationPlan.WindowedSourcePrefix.terminates checkpoint block_fallbacks
    ApplicationBindingOrigins.persistent_image_has_binding_origins (by decide) 1
    (by simp) (by decide) final hfinal

private def fixedBindingBranch (profile : SourceBehavioralProfile source.prog)
    (replacement : runtime.application.PlayerPolicy) (value : Bool) :
    FinDist runtime.application.PolicyExecution :=
  let policies := applicationPlan.windowedPlayers profile (fun _ => 10)
    bindingSelector choiceSelector (fun _ => 10) 1 replacement
  let environment := runtime.blockEnvironment [1, 0]
  (runtime.application.runPolicies policies environment [.player 1, .player 1] initial).bind
    fun middle => (runtime.application.playerStep 0 middle
      (.privateCommand (.register 0 ⟨.bool, value⟩))).bind fun registered =>
        (runtime.application.playerStep 0 registered (.submit (.binding 0 (0, 0)))).bind
          fun submitted => runtime.application.runPolicies policies environment
            [.environment, .environment, .player 1, .environment, .player 0, .environment]
            submitted

/-- A fixed source draw determines the real source successor after the complete
binding block, even with randomized raw traffic both before and after its owner. -/
theorem binding_fixed_draw_source_successor
    (profile : SourceBehavioralProfile source.prog)
    (replacement : runtime.application.PlayerPolicy) (chosen : Bool)
    (hchosen : ⟨chosen, rfl⟩ ∈ (profile 0 GeneratedBindingPolicy.site
      ((source.env.toView 0).eraseEnv)).support)
    (final : runtime.application.PolicyExecution)
    (hbranch : final ∈ (fixedBindingBranch profile replacement chosen).support) :
    ∃ sourceNext : CoupledAt GeneratedPersistentDisclosure.compiled.graph
        (compilerInitial.addCommitEvent (actionName := 0) (actionTy := BaseTy.bool)
          0 0 (.constBool true) source.fresh.1).1,
      sourceNext.current.source = source.env.cons chosen ∧
        final.native.application.base.Refines sourceNext.current.graph.1 := by
  have checkpoint := ApplicationPlan.WindowedCheckpoint.initial
    DisclosureAccounting.persistentChecked applicationPlan profile (fun _ => 10)
    bindingSelector choiceSelector (fun _ => 10) [1, 0] 1 replacement
  obtain ⟨sourceNext, hsource, _, hnext, _⟩ :=
    checkpoint.binding_fixed_branch_source_coupling _ _ profile bindingFallback 10 rfl
      (compiledInitialCoupled source) initial final
      GeneratedApplicationSourceLaw.initial_reads_public (by decide) (by simp)
      (checkpoint.referenceOwner_of_ne 0 (by decide))
      [1] [] rfl ⟨chosen, rfl⟩ hchosen (by
        change final ∈ (fixedBindingBranch profile replacement chosen).support
        exact hbranch)
  exact ⟨sourceNext, hsource, hnext.refines⟩

end VegasTests.WindowedSourceCoverage

/-- info: 'VegasTests.WindowedSourceCoverage.complete_source_execution' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.WindowedSourceCoverage.complete_source_execution

/-- info: 'VegasTests.WindowedSourceCoverage.binding_fixed_draw_source_successor'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.WindowedSourceCoverage.binding_fixed_draw_source_successor
