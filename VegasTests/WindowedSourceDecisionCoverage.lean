/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedSourceDecisionCoverage
import VegasTests.WindowedSourceCoverage
import VegasTests.GeneratedApplicationSourceLaw

/-! # Concrete source-decision coverage

The first actual persistent-disclosure block is owned by the deviating player.
Coverage of that block therefore produces an occurrence in the original source
program whose extracted policy selects the block's actual resolved value.
-/

noncomputable section

namespace VegasTests.WindowedSourceDecisionCoverage

open Vegas Vegas.EventGraph Vegas.ToEventGraph Interaction
  Interaction.MessageApplication GameTheory.Math.Probability
open VegasTests.PersistentDisclosure VegasTests.GeneratedPersistentDisclosure
open VegasTests.WindowedSourceCoverage

theorem initial_binding_has_extracted_source_choice
    (profile : SourceBehavioralProfile source.prog)
    (command : List runtime.application.PlayerEntry → runtime.application.View →
      runtime.application.PlayerCommand)
    (final : runtime.application.PolicyExecution)
    (hfinal : final ∈ (runtime.application.runPolicies
      (players profile (fun history view => FinDist.pure (command history view)))
      (runtime.blockEnvironment [0, 1])
      (WindowedApplication.blockInvocations [0, 1]) initial).support) :
    ∃ (name : VarId) (ty : simpleExpr.Ty)
      (guard : simpleExpr.Expr
        ((name, ty) :: eraseVCtx (viewVCtx (0 : TestPlayer) source.Γ)) simpleExpr.bool)
      (site : SourceDecisionSite (0 : TestPlayer) source.prog source.Γ name ty guard)
      (value : simpleExpr.Val ty)
      (legal : evalGuard guard value ((source.env.toView 0).eraseEnv) = true),
      ApplicationPlan.extractedSourcePolicy applicationPlan profile (fun _ => 10)
        bindingSelector choiceSelector (fun _ => 10) [0, 1] 0
        (fun history view => FinDist.pure (command history view))
        (compiledInitialCoupled source)
        GeneratedApplicationSourceLaw.initial_reads_public
        ApplicationBindingOrigins.persistent_image_has_binding_origins
        (by decide) (by
          intro _ _ owner _
          fin_cases owner <;> simp)
        command rfl 1 (by simp) (by decide) site ((source.env.toView 0).eraseEnv) =
          FinDist.pure ⟨value, legal⟩ := by
  let replacement : runtime.application.PlayerPolicy :=
    fun history view => FinDist.pure (command history view)
  let coupled := compiledInitialCoupled source
  have hinitial := ApplicationPlan.WindowedCheckpoint.initial
    DisclosureAccounting.persistentChecked applicationPlan profile (fun _ => 10)
    bindingSelector choiceSelector (fun _ => 10) (runtime.blockService [0, 1]) 0 replacement
  obtain ⟨Δ, nextPending, nextProg, nextAccounted, nextFresh, nextState,
      nextPlan, nextProfile, sourceNext, trace⟩ :=
    ApplicationPlan.WindowedSourcePrefix.covers hinitial block_fallbacks
      ApplicationBindingOrigins.persistent_image_has_binding_origins (by decide) 1
      (by simp) (by decide) 1 (by decide) final hfinal
  cases trace with
  | step previous block sourceStep checkpoint =>
      cases previous with
      | initial _ =>
          obtain ⟨name, ty, guard, tail, site, value, legal, _, hpolicy, _⟩ :=
            sourceStep.exists_focal_source_choice
              GeneratedApplicationSourceLaw.initial_reads_public
              ApplicationBindingOrigins.persistent_image_has_binding_origins
              (by decide) (by
                intro _ _ owner _
                fin_cases owner <;> simp)
              command rfl (relay := 1) (by simp) (by decide)
              (.initial hinitial) block checkpoint (by rfl)
          exact ⟨name, ty, guard, site, value, legal, hpolicy⟩

end VegasTests.WindowedSourceDecisionCoverage

/-- info: 'VegasTests.WindowedSourceDecisionCoverage.initial_binding_has_extracted_source_choice'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.WindowedSourceDecisionCoverage.initial_binding_has_extracted_source_choice
