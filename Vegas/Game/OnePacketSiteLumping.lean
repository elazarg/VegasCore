/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketSiteLaws

/-! # The one-step lumping for a law installed at a late site

When the profile at a site installs the late component of an option at the site
and otherwise follows a strategy that plays the certificate's components, the
owner's components along play from the site have the site shape
(`Vegas.siteComponentShape_of_installed`): at the site itself the installed
option, and later the strategy's keyed weights, since a later activation has a
longer recall and so a different key. The native kernel then lumps
(`Vegas.onePacketSiteLumping`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  [Fintype Player] {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}

/-- **The one-step lumping at late sites.** For the owner `who` and a profile
installing each option at each site, if at every site the owner plays the
certificate's components along play from the site, every binding value is a
bounded value, and the capacity is at least one and covers the late options'
slots, the native kernel lumps onto the decision image at every key with drift
twice the cube of the scale. -/
def onePacketSiteLumping
    (target : (onePacketInformation setup leaks bounds horizon
      scheduler).BehavioralAssessment) (who : Player) {LateOption' : Type}
    (profileOf : (onePacketInformation setup leaks bounds horizon scheduler).InformationSite who →
      LateOption' → ∀ player,
        (onePacketInformation setup leaks bounds horizon scheduler).BehavioralPolicy player)
    (assessment : setup.intendedModel.BehavioralAssessment)
    (covers : bounds.CoversOutputValues) (capacity : 1 ≤ bounds.candidateCount) {slots : Nat}
    (slotsLe : slots ≤ bounds.candidateCount)
    (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (options : LateKey setup leaks → LateOption' → LateKey setup leaks →
      PMF (LateOption slots))
    (shape : ∀ site key, lateKey setup leaks who site.1 = some key → ∀ option,
      SiteComponentShape assessment scale nonnegative le_one (options key option) key
        (profileOf site option) (SiteConsistent who site.1)) :
    PendingLumping target who profileOf DecisionFailed (scale ^ 3 + scale ^ 3)
      (DecisionImage (setup := setup) (leaks := leaks)) :=
  onePacketLateLumping target who profileOf
    (by have := pow_nonneg nonnegative 3; linarith) (pow_nonneg nonnegative 3)
    (by linarith) (openingKernel bounds horizon scheduler
      (fun key option => lateOpeningSilence bounds horizon scheduler assessment scale
        nonnegative le_one (options key option) key))
    (fun key option => lateBindingMoves bounds horizon scheduler scale nonnegative le_one
      (options key option) key)
    (fun site => SiteConsistent who site.1)
    (fun _ _ siteKey history _ _ => siteConsistent_of_history siteKey history)
    (fun site _ _ consistent _ member => siteConsistent_step _ who site.1 consistent member)
    (fun site key siteKey option => ownerStepClose_of_openingLaw bounds _ key option _
      (ownerOpeningLaw_of_siteComponents assessment covers scale nonnegative le_one options key
        option (profileOf site option) _ (shape site key siteKey option)))
    (fun site key siteKey option => ownerBindingLaw_of_siteComponents assessment covers capacity
      slotsLe scale nonnegative le_one options key option (profileOf site option) _
      (shape site key siteKey option))

open Classical in
/-- **The site shape of an installed late component.** Suppose a profile plays,
at a site whose key decides an event the owner has already been activated for,
the late component of an option, and elsewhere a strategy of the owner that
plays the late component of its keyed weights at activations after the first
while it has not sent for the event, and a component whose main part is the
as-if-honest choice or a mixture of late options once it has. Then the profile
has the site shape, with the installed option at the site's key and the keyed
weights at every other key. -/
theorem siteComponentShape_of_installed (assessment : setup.intendedModel.BehavioralAssessment)
    (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1) {slots : Nat} {who : Player}
    (site : (onePacketInformation setup leaks bounds horizon scheduler).InformationSite who)
    {key : LateKey setup leaks} (siteKey : lateKey setup leaks who site.1 = some key)
    (option : LateOption slots) (weights : LateKey setup leaks → PMF (LateOption slots))
    (profile : ∀ player,
      (onePacketInformation setup leaks bounds horizon scheduler).BehavioralPolicy player)
    (strategy : (onePacketInformation setup leaks bounds horizon scheduler).BehavioralPolicy who)
    (installed : profile who site.1 =
      slotTrembledChoice setup leaks bounds (initialLaw setup) horizon scheduler scale
        nonnegative le_one who site.1
        ((PMF.pure option).bind (lateChoice setup leaks bounds (initialLaw setup) horizon
          scheduler assessment who site.1))
        (PMF.pure (silenceChoice setup leaks bounds (initialLaw setup) horizon scheduler who
          site.1))
        (slotChoice setup leaks bounds (initialLaw setup) horizon scheduler assessment who
          site.1))
    (away : ∀ info, info ≠ site.1 → profile who info = strategy info)
    (activated : ∀ event, (PublicationTurn key event ∨ ∃ payload, BindingTurn key event payload) →
      ∃ entry ∈ infoRecall site.1, ActivatedAt setup leaks who event entry)
    (strategyShape : ∀ (history : (onePacketProtocol setup leaks bounds horizon
        scheduler).History) (remaining : Nat) (execution : (application setup leaks).Execution)
        (event : (graph setup).EventId),
      history.state = some ⟨remaining, some who, execution⟩ →
      ForcedState setup leaks who history.state →
      execution.application.config.cut.Ready event →
      (∃ entry ∈ execution.recall who, ActivatedAt setup leaks who event entry) →
      ((runtime setup).eventRecorded leaks (execution.recall who) event = false →
        strategy (some (execution.recall who, execution.observe (application setup leaks) who)) =
          slotTrembledChoice setup leaks bounds (initialLaw setup) horizon scheduler scale
            nonnegative le_one who (some (execution.recall who,
              execution.observe (application setup leaks) who))
            ((weights (LateKey.ofView setup leaks who (execution.recall who)
                (execution.observe (application setup leaks) who))).bind
              (lateChoice setup leaks bounds (initialLaw setup) horizon scheduler assessment who
                (some (execution.recall who, execution.observe (application setup leaks) who))))
            (PMF.pure (silenceChoice setup leaks bounds (initialLaw setup) horizon scheduler who
              (some (execution.recall who, execution.observe (application setup leaks) who))))
            (slotChoice setup leaks bounds (initialLaw setup) horizon scheduler assessment who
              (some (execution.recall who, execution.observe (application setup leaks) who)))) ∧
      ((runtime setup).eventRecorded leaks (execution.recall who) event = true →
        ∃ main : PMF ((onePacketModel setup leaks bounds (initialLaw setup) horizon
            scheduler).Choice who (some (execution.recall who,
              execution.observe (application setup leaks) who))),
          (main = honestChoice setup leaks bounds (initialLaw setup) horizon scheduler
              assessment who (some (execution.recall who,
                execution.observe (application setup leaks) who)) ∨
            ∃ others : PMF (LateOption slots), main = others.bind
              (lateChoice setup leaks bounds (initialLaw setup) horizon scheduler assessment who
                (some (execution.recall who,
                  execution.observe (application setup leaks) who)))) ∧
          strategy (some (execution.recall who,
              execution.observe (application setup leaks) who)) =
            slotTrembledChoice setup leaks bounds (initialLaw setup) horizon scheduler scale
              nonnegative le_one who (some (execution.recall who,
                execution.observe (application setup leaks) who)) main
              (PMF.pure (silenceChoice setup leaks bounds (initialLaw setup) horizon scheduler
                who (some (execution.recall who,
                  execution.observe (application setup leaks) who))))
              (slotChoice setup leaks bounds (initialLaw setup) horizon scheduler assessment who
                (some (execution.recall who,
                  execution.observe (application setup leaks) who))))) :
    SiteComponentShape assessment scale nonnegative le_one
      (fun other => if other = key then PMF.pure option else weights other) key profile
      (SiteConsistent who site.1) := by
  have ownerEq : key.owner = who := owner_of_lateKey siteKey
  subst ownerEq
  intro event turn history remaining execution current consistent forced ready
  rw [current] at consistent
  by_cases atSite : (application setup leaks).observe key.owner
      (some ⟨remaining, some key.owner, execution⟩) = site.1
  · have infoEq : site.1 = some (execution.recall key.owner,
        execution.observe (application setup leaks) key.owner) := by
      rw [← atSite]
      simp only [ReactiveApplication.observe, ↓reduceIte]
    have keyEq : LateKey.ofView setup leaks key.owner (execution.recall key.owner)
        (execution.observe (application setup leaks) key.owner) = key := by
      rw [infoEq] at siteKey
      exact Option.some.inj siteKey
    rw [infoEq] at installed
    constructor
    · intro _
      rw [installed]
      beta_reduce
      rw [keyEq]
      simp only [↓reduceIte]
    · intro _
      exact ⟨_, Or.inr ⟨PMF.pure option, rfl⟩, installed⟩
  · have notSite : some (execution.recall key.owner,
        execution.observe (application setup leaks) key.owner) ≠ site.1 := by
      intro same
      apply atSite
      rw [← same]
      simp only [ReactiveApplication.observe, ↓reduceIte]
    have keyNe : LateKey.ofView setup leaks key.owner (execution.recall key.owner)
        (execution.observe (application setup leaks) key.owner) ≠ key := fun same =>
      atSite (siteConsistent_key siteKey consistent same)
    have longer : ∃ entry rest, execution.recall key.owner =
        infoRecall site.1 ++ entry :: rest := by
      rcases consistent with ⟨_, sameInfo⟩ | longer
      · exact (atSite sameInfo).elim
      · exact longer
    obtain ⟨activation, member, activatedAt⟩ := activated event turn
    have recalledActivation : ∃ entry ∈ execution.recall key.owner,
        ActivatedAt setup leaks key.owner event entry := by
      obtain ⟨entry, rest, recallEq⟩ := longer
      exact ⟨activation, by rw [recallEq]; exact List.mem_append_left _ member, activatedAt⟩
    have shapes := strategyShape history remaining execution event current forced ready
      recalledActivation
    rw [away _ notSite]
    beta_reduce
    simp only [keyNe, ↓reduceIte]
    exact shapes

end Vegas
