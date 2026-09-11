/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedDeviationLaw
import Vegas.Compile.WindowedMixedDeviation
import VegasTests.WindowedSourceCoverage

/-! # Whole-law regressions for windowed unilateral deviations -/

noncomputable section

namespace VegasTests.WindowedDeviationLaw

open Vegas Vegas.EventGraph Vegas.ToEventGraph Interaction
  Interaction.MessageApplication GameTheory GameTheory.Math.Probability
open VegasTests.PersistentDisclosure VegasTests.GeneratedPersistentDisclosure
open VegasTests.WindowedSourceCoverage

def deviationSourcePolicy (profile : SourceBehavioralProfile source.prog)
    (command : List runtime.application.PlayerEntry → runtime.application.View →
      runtime.application.PlayerCommand) : SourceBehavioralPolicy source.prog 0 :=
  applicationPlan.extractedSourcePolicy profile (fun _ => 10) bindingSelector choiceSelector
    (fun _ => 10) [0, 1] 0 (fun history view => FinDist.pure (command history view))
    (compiledInitialCoupled source) GeneratedApplicationSourceLaw.initial_reads_public
    ApplicationBindingOrigins.persistent_image_has_binding_origins (by decide) (by
      intro _ _ owner _
      fin_cases owner <;> simp)
    command rfl 1 (by simp) (by decide)

/-- The six-block mixed-feature runtime has exactly the source public outcome
law after replacing player zero by an arbitrary pure raw command policy. -/
theorem persistent_pure_deviation_public_law
    (profile : SourceBehavioralProfile source.prog)
    (command : List runtime.application.PlayerEntry → runtime.application.View →
      runtime.application.PlayerCommand) :
    ((runtime.application.runPolicies
      (players profile (fun history view => FinDist.pure (command history view)))
      (runtime.blockEnvironment [0, 1])
      (List.replicate 6 (WindowedApplication.blockInvocations [0, 1])).flatten initial).map
        fun out : runtime.application.PolicyExecution =>
          (out.native.application.base.memory.finished
              GeneratedPersistentDisclosure.compiled.graph.nodeCount,
            GeneratedPersistentDisclosure.compiled.readPublicTerminal?
              out.native.application.base.memory)) =
      (denoteSource source.prog
        (Profile.update (sig := sourceGameSignature source.prog) profile 0
          (deviationSourcePolicy profile command)) source.env).map fun terminal =>
        (true, some (cast (congrArg (VEnv simpleExpr)
          (compileCore_terminalCtx_eq_sourceTerminalCtx source.prog source.fresh
            compilerInitial).symm) terminal).erasePubEnv) := by
  have hlaw := ApplicationPlan.windowed_pure_deviation_source_public_law
    DisclosureAccounting.persistentChecked applicationPlan profile (fun _ => 10)
    bindingSelector choiceSelector (fun _ => 10) [0, 1] 0
    GeneratedApplicationSourceLaw.initial_reads_public
    ApplicationBindingOrigins.persistent_image_has_binding_origins block_fallbacks
    (by decide) (by
      intro _ _ owner _
      fin_cases owner <;> simp)
    command 1 (by simp) (by decide)
  exact hlaw

/-- An arbitrary randomized player-zero policy has the public outcome law of
a finite mixture of legal source behavioral deviations. -/
theorem persistent_randomized_deviation_public_mixture
    (profile : SourceBehavioralProfile source.prog)
    (replacement : runtime.application.PlayerPolicy) :
    ∃ sourceMixture : FinDist (SourceBehavioralPolicy source.prog 0),
      ((runtime.application.runPolicies
        (players profile replacement)
        (runtime.blockEnvironment [0, 1])
        (List.replicate 6 (WindowedApplication.blockInvocations [0, 1])).flatten initial).map
          fun out : runtime.application.PolicyExecution =>
            (out.native.application.base.memory.finished
                GeneratedPersistentDisclosure.compiled.graph.nodeCount,
              GeneratedPersistentDisclosure.compiled.readPublicTerminal?
                out.native.application.base.memory)) =
        sourceMixture.bind fun sourceReplacement =>
          (denoteSource source.prog
            (Profile.update (sig := sourceGameSignature source.prog) profile 0
              sourceReplacement) source.env).map fun terminal =>
            (true, some (cast (congrArg (VEnv simpleExpr)
              (compileCore_terminalCtx_eq_sourceTerminalCtx source.prog source.fresh
                compilerInitial).symm) terminal).erasePubEnv) := by
  exact ApplicationPlan.windowed_deviation_source_public_mixture
    DisclosureAccounting.persistentChecked applicationPlan profile (fun _ => 10)
    bindingSelector choiceSelector
    (fun _ => 10) [0, 1] 0 GeneratedApplicationSourceLaw.initial_reads_public
    ApplicationBindingOrigins.persistent_image_has_binding_origins block_fallbacks
    (by decide) (by
      intro _ _ owner _
      fin_cases owner <;> simp)
    replacement 1 (by simp) (by decide)

end VegasTests.WindowedDeviationLaw

/-- info: 'VegasTests.WindowedDeviationLaw.persistent_pure_deviation_public_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.WindowedDeviationLaw.persistent_pure_deviation_public_law

/-- info: 'VegasTests.WindowedDeviationLaw.persistent_randomized_deviation_public_mixture'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.WindowedDeviationLaw.persistent_randomized_deviation_public_mixture
