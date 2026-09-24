/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveAuthorization
import VegasTests.ReactiveEarlyOpeningEvaluation

/-! # Dependency authorization excludes the premature disclosure envelopes

The raw early-opening fixture still broadcasts and retains these packets.
Their original submission views lack the binding predecessor. Completion of
that predecessor does not authorize them; a fresh later opening is authorized.
These are authorization results, not an SPE theorem for a constructed service.
-/

noncomputable section

namespace VegasTests.ReactiveEarlyOpening

open GameTheory.Math.Probability Interaction Vegas Vegas.EventGraphRuntime

def withholdingEnvelope : Message Unit (WitnessedPacket graph) := ⟨((), 1), ⟨.withhold 1, none⟩⟩
def prematureOpeningEnvelope : Message Unit (WitnessedPacket graph) :=
  ⟨((), 2), ⟨.opening 1 ((), .prepared 0) ⟨.int, 1⟩,
    some ⟨((), .prepared 0), ⟨.int, 1⟩⟩⟩⟩

def withholdingOrigin : app.PlayerEntry :=
  ⟨(activated (afterFirst first)).observe app (), second, some withholdingEnvelope⟩
def prematureOpeningOrigin : app.PlayerEntry :=
  ⟨(activated contested).observe app (), earlyOpening, some prematureOpeningEnvelope⟩

theorem withholding_origin : contested.submissionOrigin? app withholdingEnvelope.id =
    some withholdingOrigin := rfl

theorem premature_opening_origin :
    (afterResponse false).submissionOrigin? app prematureOpeningEnvelope.id =
      some prematureOpeningOrigin := rfl

theorem withholding_unauthorized :
    ¬ contested.AuthorizedAtSubmission app (runtime.submissionDependencyCondition leaks)
      withholdingEnvelope :=
  runtime.premature_not_authorized leaks contested withholdingEnvelope withholdingOrigin
    withholding_origin 1 0 rfl (by decide) (by decide)

theorem premature_opening_unauthorized :
    ¬ (afterResponse false).AuthorizedAtSubmission app (runtime.submissionDependencyCondition leaks)
      prematureOpeningEnvelope :=
  runtime.premature_not_authorized leaks _ prematureOpeningEnvelope prematureOpeningOrigin
    premature_opening_origin 1 0 rfl (by decide) (by decide)

/-- Making the dependency ready does not renew the first envelope's authority. -/
theorem withholding_unauthorized_after_binding (repair fresh : Bool) :
    ¬ (granted repair fresh).AuthorizedAtSubmission app
      (runtime.submissionDependencyCondition leaks)
      withholdingEnvelope := by
  apply runtime.premature_not_authorized leaks _ withholdingEnvelope withholdingOrigin _ 1 0
    rfl (by decide) (by decide)
  cases repair <;> cases fresh <;> rfl

theorem premature_opening_unauthorized_after_binding :
    ¬ (granted false false).AuthorizedAtSubmission app (runtime.submissionDependencyCondition leaks)
      prematureOpeningEnvelope :=
  runtime.premature_not_authorized leaks _ prematureOpeningEnvelope prematureOpeningOrigin
    rfl 1 0 rfl (by decide) (by decide)

/-- The same opening payload in a new envelope after inclusion is authorized. -/
theorem later_opening_authorized :
    (disclosed false false).AuthorizedAtSubmission app (runtime.submissionDependencyCondition leaks)
      ⟨((), 3), ⟨.opening 1 ((), .prepared 0) ⟨.int, 1⟩,
        some ⟨((), .prepared 0), ⟨.int, 1⟩⟩⟩⟩ := by
  have ready : (activated (granted false false)).application.publicView.EventReady 1 := by
    rw [State.publicView_eventReady]
    exact disclosure_ready false false (by simp)
  have authorized := runtime.ready_submission_authorized leaks
    (activated (granted false false)) ()
    (disclosureSubmission (.opening 1 (candidate false) ⟨.int, selectedValue false⟩))
    1 rfl ready rfl
  change (disclosed false false).AuthorizedAtSubmission app
    (runtime.submissionDependencyCondition leaks)
    ⟨((), 3),
      (disclosureSubmission (.opening 1 (candidate false) ⟨.int, selectedValue false⟩)).emit
        (granted false false).application () ((granted false false).network.known ())⟩ at authorized
  rw [final_opening_emitted false false (by simp)] at authorized
  exact authorized

/-- Authorization is not a restriction on broadcast or pending storage. -/
theorem premature_opening_pending :
    prematureOpeningEnvelope ∈ (afterResponse false).network.pending := by
  exact List.mem_append_right _ (List.mem_singleton_self _)

end VegasTests.ReactiveEarlyOpening
