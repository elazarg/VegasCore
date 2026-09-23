/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.ReactivePendingMenusStrategies

/-! # A source SPE has no utility-independent reactive translation

The source and graph are the same bind-and-disclose game. Two public-result
utilities share one source SPE, under either commitment-admission interface.
The specified reactive scheduler admits no common native behavioral SPE.
This rules out utility-independent translation into this particular service;
it does not rule out preservation under stronger service contracts.
-/

noncomputable section

namespace VegasTests.ReactivePendingMenus

open GameTheory GameTheory.Protocol GameTheory.Math.Probability Interaction Vegas
open Vegas.SourceProgram

/-- Even an arbitrary whole-profile translator cannot preserve SPE for both
utilities in this game and service. In particular, no playerwise compiler can.
All commitments used in the witnessing prefix are valid and fixed at submission. -/
theorem no_utility_independent_spe_compiler
    (admission : CommitmentInterface PendingMenus.sourceProgram) :
    ¬ ∃ compile : Profile (PendingMenus.sourceModel admission).behavioralSignature →
        Profile model.behavioralSignature,
      ∀ preferOne,
        (PendingMenus.sourceModel admission).IsBehavioralSubgamePerfect
          (protocol_singleMover PendingMenus.sourceProgram admission PendingMenus.sourceInitial)
          (protocol_bounded PendingMenus.sourceProgram admission PendingMenus.sourceInitial)
          (PendingMenus.sourceProtocolProfile admission)
          (protocolUtility PendingMenus.sourceProgram admission PendingMenus.sourceInitial
            (PendingMenus.sourceUtility preferOne)) →
        model.IsBehavioralSubgamePerfect (app.singleMover (FinDist.pure initialState) 7 scheduler)
          (app.bounded (FinDist.pure initialState) 7 scheduler)
          (compile (PendingMenus.sourceProtocolProfile admission)) (payoff preferOne) := by
  rintro ⟨compile, preserves⟩
  exact no_common_spe ⟨compile (PendingMenus.sourceProtocolProfile admission),
    preserves true (PendingMenus.source_spe admission true),
    preserves false (PendingMenus.source_spe admission false)⟩

end VegasTests.ReactivePendingMenus
