/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceDecisionSupport

/-! # Actual retained histories at a phase grant

The next grant uniquely selects the completed source prefix. Its real retained
history therefore supplies the full typed boundary, including readiness and
the absence of submissions for future events. Empty response rosters require
no special case or additional service assumption.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory.Math.Probability GameTheory.Protocol Interaction EventGraphRuntime EventLowering

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

private theorem rosterBlock_grant
    (setup : Setup (Player := Player) (L := L))
    (rosters : (graph setup).EventId → List Player)
    (block event : (graph setup).EventId) (index : Nat)
    (found : (rosterBlock setup rosters block)[index]? = some (.grant event)) :
    block = event ∧ index = 0 := by
  change ([.grant block] ++ (rosters block).map ServiceInstruction.player ++
    (match (graph setup).actor? block with
    | none => [.sample block]
    | some actor => [.includeLatest block actor]) ++
      List.replicate (block.val + 1) .tick ++ [.expire block])[index]? = _ at found
  simp only [List.append_assoc, List.cons_append, List.nil_append] at found
  cases index with
  | zero =>
      exact ⟨ServiceInstruction.grant.inj (Option.some.inj found), rfl⟩
  | succ index =>
      simp only [List.getElem?_cons_succ] at found
      have member := List.mem_of_getElem? found
      simp only [List.mem_append, List.mem_map, List.mem_replicate, List.mem_singleton] at member
      rcases member with ⟨actor, _, impossible⟩ | middle | ⟨_, impossible⟩ | impossible
      · cases impossible
      · cases owned : (graph setup).actor? block <;> simp only [owned, List.mem_singleton] at middle
        all_goals cases middle
      · cases impossible
      · cases impossible

/-- Grants occur exactly after the preceding complete event blocks. -/
theorem roster_grant_prefix
    (setup : Setup (Player := Player) (L := L))
    (rosters : (graph setup).EventId → List Player)
    (index : Nat) (event : (graph setup).EventId)
    (found : (rosterPlan setup rosters)[index]? = some (.grant event)) :
    index = (rosterPlanPrefix setup rosters event.val).length ∧
      (rosterPlan setup rosters).take index = rosterPlanPrefix setup rosters event.val := by
  obtain ⟨rank, block, offset, selected, located, position⟩ := flatMap_position
    (List.finRange (graph setup).order.eventCount) (rosterBlock setup rosters) index
      (.grant event) found
  obtain ⟨blockEq, offsetEq⟩ := rosterBlock_grant setup rosters block event offset located
  subst block
  subst offset
  have bound := (List.getElem?_eq_some_iff.mp selected).1
  rw [List.getElem?_eq_getElem bound, List.getElem_finRange] at selected
  have rankEq : rank = event.val := congrArg Fin.val (Option.some.inj selected)
  have indexEq : index = (rosterPlanPrefix setup rosters event.val).length := by
    change index = (rosterPlanPrefix setup rosters rank).length + 0 at position
    simpa only [rankEq, Nat.add_zero] using position
  refine ⟨indexEq, ?_⟩
  obtain ⟨after, split⟩ := rosterPlan_split setup rosters event
  rw [indexEq, split, List.append_assoc, List.take_left]

variable [Fintype Player]

/-- Every actual pre-grant retained history is itself a complete typed source
boundary. All operational resources are inherited from the source-prefix proof. -/
theorem sourceService_grant_boundary
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : BindingOpportunities setup rosters)
    (network : (runtime setup).NetworkPolicy leaks)
    (control : (application setup leaks).Control)
    (trace : ((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
        (some control)) (idle : control.actor = none)
    (event : (graph setup).EventId)
    (selected : (rosterPlan setup rosters)[control.execution.environmentRecall.length]? =
      some (.grant event)) :
    ∃ initial ∈ setup.initialLaw.support, ∃ (Γ : SourceCtx Player L)
      (source : Config Player L Γ) (refs : ContextRefs (graph setup).layout Γ),
      ServiceBoundary setup leaks rosters initial source refs event.val control.execution := by
  let menu := sourceServiceMenu setup leaks bounds rosters
  obtain ⟨_, planPrefix⟩ := roster_grant_prefix setup rosters _ event selected
  have supported := menu.roundSupported_uniform (initialLaw setup)
    (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network) trace
  have account := supported.1
  have reached := supported.2
  rw [idle] at reached
  change control.execution ∈ ((application setup leaks).roundsFrom (initialLaw setup)
    (rosterScheduler setup leaks rosters network) menu.uniformResponses
      control.execution.environmentRecall.length).support at reached
  have within : control.execution.environmentRecall.length ≤ (rosterPlan setup rosters).length :=
    by omega
  rw [roster_roundsFrom setup leaks rosters network menu.uniformResponses _ within, planPrefix]
    at reached
  obtain ⟨initial, initialSupport, _, _, _, Γ, names, remaining, remainingProfile, source,
      refs, embedding, refsBefore, _, _, _, _, _, _, _, _, checkpoint⟩ :=
    initialized_sourceService_prefix_support setup leaks bounds values capacity rosters
      opportunities menu.uniformResponses
      (fun who past view response member =>
        (menu.uniformResponses_support who past view response).mp member)
      network (failureProfile setup.program) event.val event.isLt.le control.execution reached
  exact ⟨initial, initialSupport, Γ, source, refs, checkpoint⟩

end Vegas.SourceProgram.RevealService
