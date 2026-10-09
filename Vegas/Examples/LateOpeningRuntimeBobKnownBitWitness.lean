/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeBobBindingWitness
import Vegas.Examples.LateOpeningRuntimeBobKnownBit

/-! # A genuine certificate-bearing failed-publication information class

Alice sends her certified opening at the first late activation, Bob's fair
pending sample discloses it, and the lottery then omits the packet. Alice's
publication expires. The authentic certificate remains visible when Bob is
asked to bind his answer. This constructs a real information site of the
complete bounded raw runtime for each initialized bit and private label.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeBobKnownBitWitness

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeBobKnownBit

/-- The known-bit rationality result has a genuine native information class
even though Alice's opening has no successful publication receipt. -/
theorem failed_publication_known_bit_class (weight : ℝ) (nonnegative : 0 ≤ weight)
    (bit : Bool) (label : Fin 3) :
    ∃ (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
      (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
        bob site.1)
      (decision : LateOpeningRuntimeBobBindingInformation.DecisionHistory weight nonnegative),
      representative.1.state = some ⟨14, some bob, decision.execution⟩ ∧
        EventGraphRuntime.State.Invariant (graph := nativeGraph)
          (setup.eventInputs (sourceInitial bit label)) decision.execution.application ∧
        ObservesBit (decision.execution.observe app bob) bit := by
  obtain ⟨site, representative, decision, current, initialized, observed⟩ :=
    LateOpeningRuntimeBobBindingWitness.failed_binding_information_representative
      weight nonnegative bit label true
  exact ⟨site, representative, decision, current, initialized, observed rfl⟩

end Vegas.Examples.LateOpeningRuntimeBobKnownBitWitness
