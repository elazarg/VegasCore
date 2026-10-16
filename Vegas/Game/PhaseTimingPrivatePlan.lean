/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingKeyRecall
import Interaction.ReactivePolicyMixture

/-! # Original timing-plan coordinates at actual owner inputs -/

noncomputable section

namespace Vegas

open Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (bounds : MessageBounds graph)

local notation "app" => phaseApplication runtime leaks

open Classical in
/-- The selected coordinate is read only at its own complete operational key.
The remainder may retain complete source words and every other timing choice. -/
def phaseTimingPlanMember {Rest : Type} (who : Player)
    (selected : Option (PhaseTimingKey graph))
    (other : Rest → Option (PhaseTimingKey graph) → LateOption bounds.candidateCount)
    (component : Rest → LateOption bounds.candidateCount → (app).Policy)
    (memory : LateOption bounds.candidateCount × Rest) : (app).Policy := fun past view =>
  let key := phaseTimingKey runtime leaks who (some (past, view))
  component memory.2 (if key = selected then memory.1 else other memory.2 key) past view

/-- A private timing plan retains the actual component's bounded one-packet
coverage at every input, including inputs outside initialized play. -/
theorem phaseTimingPlanMember_covered {Rest : Type} (who : Player)
    (selected : Option (PhaseTimingKey graph))
    (other : Rest → Option (PhaseTimingKey graph) → LateOption bounds.candidateCount)
    (component : Rest → LateOption bounds.candidateCount → (app).Policy)
    (covered : ∀ rest option past view response,
      response ∈ (component rest option past view).support →
        response ∈ PhaseCount.onePacketActions runtime leaks bounds who past view)
    (memory : LateOption bounds.candidateCount × Rest)
    (past : List (app).PlayerEntry) (view : (app).PlayerView) (response : (app).Action)
    (supported : response ∈ (phaseTimingPlanMember runtime leaks bounds who selected other
      component memory past view).support) :
    response ∈ PhaseCount.onePacketActions runtime leaks bounds who past view := by
  exact covered memory.2 _ past view response supported

omit [Fintype Player] in
/-- The current timing coordinate retains its ORIGINAL weight law independently
of the complete updated remainder at the actual owner input. The member laws
may randomize; past WAIT and SEND records remain in the full recall. -/
theorem phaseTimingPlan_realization {Rest : Type} (who : Player)
    (weights : PMF (LateOption bounds.candidateCount)) (restLaw : PMF Rest)
    (other : Rest → Option (PhaseTimingKey graph) → LateOption bounds.candidateCount)
    (component : Rest → LateOption bounds.candidateCount → (app).Policy)
    (past : List (app).PlayerEntry) (view : (app).PlayerView) :
    let selected := phaseTimingKey runtime leaks who (some (past, view))
    let remainder := fun rest before earlierView => component rest
      (other rest (phaseTimingKey runtime leaks who (some (before, earlierView))))
        before earlierView
    let remembered := ((app).policyMixture restLaw remainder).posterior past
    let members := phaseTimingPlanMember runtime leaks bounds who selected other component
    ((app).policyMixture (weights.bind fun option => restLaw.map (Prod.mk option))
      members).posterior past = weights.bind (fun option => remembered.map (Prod.mk option)) ∧
    ((app).policyMixture (weights.bind fun option => restLaw.map (Prod.mk option))
      members).policy past view = weights.bind (fun option => remembered.bind
        (fun rest => component rest option past view)) := by
  classical
  intro selected remainder remembered members
  have unchanged : ((app).policyMixture
      (weights.bind fun option => restLaw.map (Prod.mk option)) members).posterior past =
      weights.bind (fun option => remembered.map (Prod.mk option)) := by
    apply (app).policyMixture_posterior_independent_left weights restLaw members remainder past
    intro before entry earlier option rest
    have fresh := phaseTimingKey_fresh runtime leaks who past before view entry earlier
    change component rest (if phaseTimingKey runtime leaks who (some (before, entry.beforeView)) =
      selected then option else other rest
        (phaseTimingKey runtime leaks who (some (before, entry.beforeView))))
          before entry.beforeView =
      remainder rest before entry.beforeView
    rw [ite_eq_right fresh]
  refine ⟨unchanged, ?_⟩
  rw [ReactiveApplication.policyMixture_policy, unchanged, PMF.bind_bind]
  apply bind_congr_on_support
  intro option _supported
  rw [PMF.bind_map]
  apply bind_congr_on_support
  intro rest _possible
  change component rest (if phaseTimingKey runtime leaks who (some (past, view)) = selected
    then option else other rest (phaseTimingKey runtime leaks who (some (past, view))))
      past view = _
  rw [ite_eq_left rfl]

end Vegas
