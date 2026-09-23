/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.ReactiveMenusSPE
import VegasTests.PendingMenusSource

/-! # Source-to-reactive impossibility for utility-independent SPE compilation

The source policy binds zero and always discloses. It is an SPE for both public
utilities under either commitment admission. No reactive target profile is an
SPE for both, so no utility-independent translation of this source game into
this service preserves SPE for all public utilities. The quantification allows
whole-profile translation, which includes playerwise compilation.

`PendingMenus.source_graph_publication` checks the public semantic connection
between the source program and the explicit two-event graph used here.
-/

noncomputable section

namespace VegasTests.ReactiveMenus

open GameTheory GameTheory.Protocol Vegas Vegas.SourceProgram

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
        model.IsBehavioralSubgamePerfect
          (app.singleMover initialLaw horizon scheduler)
          (app.bounded initialLaw horizon scheduler)
          (compile (PendingMenus.sourceProtocolProfile admission)) (reactivePayoff preferOne) := by
  rintro ⟨compile, preserves⟩
  exact no_common_reactive_spe ⟨compile (PendingMenus.sourceProtocolProfile admission),
    preserves true (PendingMenus.source_spe admission true),
    preserves false (PendingMenus.source_spe admission false)⟩

end VegasTests.ReactiveMenus
