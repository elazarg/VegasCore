/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.OpaqueBindingForkVanishingWait
import Vegas.Game.SourceServiceFirstInputSourceLaw

/-! # Source readout at the delayed opaque Bob input

The two delayed histories have the same complete typed configuration. The
actual posterior at their shared Bob input therefore restores exactly the
same initial parameter and source prefix, even though Alice's private-risk
posterior is nondegenerate. This does not constrain future free policies.
-/

noncomputable section

namespace Vegas.OpaqueBindingFork

open SourceProgram EventGraphRuntime Interaction GameTheory.Math.Probability

/-- The private timestamp distinction lives outside the typed graph state. -/
theorem bob_config_eq : cleanBob.application.config = riskyBob.application.config := by
  have applicationEq := accepted_fields_eq.1
  change cleanAccepted.application.config = riskyAccepted.application.config
  exact congrArg EventGraphRuntime.State.config applicationEq

/-- Before any resolution, both physical decoders and the common all-owner
original-memory lottery use exactly the same actual typed state. -/
theorem bob_source_readout_eq {Parameter : Type}
    (profile : BehavioralProfile setup.program)
    (parameter : State simpleExpr setup.context → Parameter) :
    sourceServiceRestoredPrefixReadout profile parameter bobResolution.val
        cleanBob.application.config =
      sourceServiceRestoredPrefixReadout profile parameter bobResolution.val
        riskyBob.application.config := congrArg _ bob_config_eq

/-- The persistent initialization decoder recovers the actual source draw. -/
theorem bob_initial_readout : sourceInitialReadout setup cleanBob.application.config =
    some sourceInitial := by
  change sourceInitialReadout setup cleanAccepted.application.config = some sourceInitial
  rw [accepted_application_eq, riskyAccepted_config]
  exact sourceInitialReadout_eq_some_of_inputs setup _ sourceInitial rfl

/-- The actual completed three-instruction prefix decodes successfully. -/
theorem bob_source_prefix_present : (sourceServicePrefix? setup bobResolution.val
    cleanBob.application.config).isSome = true := by
  change (sourceServicePrefix? setup bobResolution.val cleanAccepted.application.config).isSome =
    true
  rw [accepted_application_eq, riskyAccepted_config]
  decide

namespace VanishingWait

variable (alpha : ℝ) (nonnegative : 0 ≤ alpha) (small : alpha ≤ 1)

/-- The actual whole Bob input, including his chronological response recall. -/
def bobReadout (execution : app.Execution) : BobInput :=
  (execution.recall bob, execution.observe app bob)

private theorem beforeBob_late_mass :
    ((beforeBob alpha nonnegative small).map bobReadout) bobInput = ENNReal.ofReal alpha := by
  have projected : (joint alpha nonnegative small).map Prod.fst =
      (beforeBob alpha nonnegative small).map bobReadout := by
    rw [joint, PMF.map_comp]
    rfl
  rw [← projected]
  exact joint_late_mass alpha nonnegative small

private theorem late_support (positive : 0 < alpha) :
    bobInput ∈ ((beforeBob alpha nonnegative small).map bobReadout).support := by
  rw [PMF.mem_support_iff, beforeBob_late_mass]
  exact (ENNReal.ofReal_pos.mpr positive).ne'

/-- Conditioning on the actual delayed Bob input retains only the two real
delayed states, whose complete typed configuration is identical. -/
theorem late_config_supported (positive : 0 < alpha) (execution : app.Execution)
    (supported : execution ∈ (fiberPosterior (beforeBob alpha nonnegative small)
      bobReadout bobInput).support) :
    execution.application.config = cleanBob.application.config := by
  have actual := mem_support_fiberPosterior (late_support alpha nonnegative small positive)
    supported
  rw [beforeBob_eq] at actual
  rcases support_mix_subset alpha nonnegative small _ _ actual.2 with delayed | immediate
  · rcases support_mix_subset (1 / 2) (by norm_num) (by norm_num) _ _ delayed with clean | risky
    · cases (PMF.mem_support_pure_iff _ _).mp clean
      rfl
    · cases (PMF.mem_support_pure_iff _ _).mp risky
      exact bob_config_eq.symm
  · rcases support_mix_subset (1 / 2) (by norm_num) (by norm_num) _ _ immediate with first | second
    · cases (PMF.mem_support_pure_iff _ _).mp first
      exact (immediateBob_input_ne_clean actual.1).elim
    · cases (PMF.mem_support_pure_iff _ _).mp second
      have same := actual.1
      change (immediateOtherBob.recall bob, immediateOtherBob.observe app bob) = bobInput at same
      rw [immediateOtherBob_input_eq] at same
      exact (immediateBob_input_ne_clean same).elim

/-- The actual posterior on the complete graph state has no hidden-risk
mixture: Alice's differing private recall does not alter this typed prefix. -/
theorem late_config_posterior (positive : 0 < alpha) :
    (fiberPosterior (beforeBob alpha nonnegative small) bobReadout bobInput).map
      (fun execution => execution.application.config) = PMF.pure cleanBob.application.config := by
  calc
    _ = (fiberPosterior (beforeBob alpha nonnegative small) bobReadout bobInput).map
        (fun _ => cleanBob.application.config) := by
      apply map_congr_on_support
      exact late_config_supported alpha nonnegative small positive
    _ = _ := PMF.map_const _ _

/-- Restore the original source histories in one common actual decoder lottery.
Its conditional law equals the clean witness's lottery, retaining the same
persistent initial parameter. Physical Alice recall is not restored. -/
theorem late_source_posterior {Parameter : Type}
    (positive : 0 < alpha) (profile : BehavioralProfile setup.program)
    (parameter : State simpleExpr setup.context → Parameter) :
    (fiberPosterior (beforeBob alpha nonnegative small) bobReadout bobInput).bind
        (fun execution => sourceServiceRestoredPrefixReadout profile parameter bobResolution.val
          execution.application.config) =
      sourceServiceRestoredPrefixReadout profile parameter bobResolution.val
        cleanBob.application.config := by
  calc
    _ = (fiberPosterior (beforeBob alpha nonnegative small) bobReadout bobInput).bind
        (fun _ => sourceServiceRestoredPrefixReadout profile parameter bobResolution.val
          cleanBob.application.config) := by
      apply bind_congr_on_support
      intro execution supported
      rw [late_config_supported alpha nonnegative small positive execution supported]
    _ = _ := PMF.bind_const _ _

/-- Both physical decoders succeed; the conditional carrier uses the actual
initial state and one all-owner restoration of the actual typed source prefix. -/
theorem late_source_posterior_decoded {Parameter : Type}
    (positive : 0 < alpha) (profile : BehavioralProfile setup.program)
    (parameter : State simpleExpr setup.context → Parameter) :
    ∃ before : ProtocolState setup.program,
      sourceServicePrefix? setup bobResolution.val cleanBob.application.config = some before ∧
      (fiberPosterior (beforeBob alpha nonnegative small) bobReadout bobInput).bind
          (fun execution => sourceServiceRestoredPrefixReadout profile parameter bobResolution.val
            execution.application.config) =
        (profile.restoreDisclosureMemory setup.program [] (Revelations.initial setup.context)
          before).map (fun original => some (parameter sourceInitial, original)) := by
  obtain ⟨before, decoded⟩ := Option.isSome_iff_exists.mp bob_source_prefix_present
  refine ⟨before, decoded, ?_⟩
  rw [late_source_posterior alpha nonnegative small positive profile parameter]
  simp only [sourceServiceRestoredPrefixReadout, bob_initial_readout, decoded]

end VanishingWait
end Vegas.OpaqueBindingFork
