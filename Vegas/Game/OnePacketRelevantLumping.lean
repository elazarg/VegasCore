/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketSiteLaws

/-! # One-step lumping at relevant sites

`Vegas.PendingLumping` asks for its one-step lumping at every site with a
late-delivery key. A profile need only be lumped at the sites one uses, such as
the late deliveries: at a first activation the key still decides an event, but
the owner plays its prescribed component rather than a late component.
`Vegas.PendingLumpingOn` asks for the lumping only at sites satisfying a
predicate `relevant`, and gives the same pathwise failure bound there
(`Vegas.PendingLumpingOn.pathwise`). The native kernel lumps onto the decision
image at the relevant sites whose owner steps and laws of moves are close to
keyed kernels at allowed states (`Vegas.onePacketLateLumpingOn`).
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

open Classical in
/-- **One-step lumping at relevant sites.** `Vegas.PendingLumping` with every
site-indexed requirement asked only at the sites satisfying `relevant`. -/
structure PendingLumpingOn (assessment : (onePacketInformation setup leaks bounds horizon
      scheduler).BehavioralAssessment) (who : Player)
    (relevant : (onePacketInformation setup leaks bounds horizon scheduler).InformationSite who →
      Prop) {LateOption : Type}
    (profileOf : (onePacketInformation setup leaks bounds horizon scheduler).InformationSite who →
      LateOption → ∀ player,
        (onePacketInformation setup leaks bounds horizon scheduler).BehavioralPolicy player)
    (failedState : LateKey setup leaks → (application setup leaks).ProtocolState → Prop) (δ : ℝ)
    (Y : Type) where
  /-- The image of a protocol state at a key. -/
  image : LateKey setup leaks → (application setup leaks).ProtocolState → Y
  /-- The image kernel of a key and an option. -/
  kernel : LateKey setup leaks → LateOption → Y → PMF Y
  /-- The image of a forced history's state, read off its operational record. -/
  start : LateKey setup leaks → List (Option (OperationalState setup leaks)) → Y
  /-- The kept states for a site and its key. -/
  keep : (onePacketInformation setup leaks bounds horizon scheduler).InformationSite who →
    LateKey setup leaks → Set (application setup leaks).ProtocolState
  /-- Failure as a function of the image. -/
  failure : LateKey setup leaks → Y → ℝ
  failure_unit : ∀ key y, 0 ≤ failure key y ∧ failure key y ≤ 1
  start_eq : ∀ site, relevant site → ∀ key, lateKey setup leaks who site.1 = some key →
    ∀ history ∈ (assessment.belief who site).support,
      ForcedState setup leaks who history.1.state →
        image key history.1.state =
          start key (operationalRecord setup leaks bounds horizon scheduler history.1.trace)
  start_kept : ∀ site, relevant site → ∀ key, lateKey setup leaks who site.1 = some key →
    ∀ history ∈ (assessment.belief who site).support,
      ForcedState setup leaks who history.1.state → history.1.state ∈ keep site key
  kept : ∀ site, relevant site → ∀ key, lateKey setup leaks who site.1 = some key → ∀ option,
    ∀ state ∈ keep site key, ∀ next ∈ ((application setup leaks).controlStep (initialLaw setup)
      horizon scheduler ((bounds.onePacketMenu (runtime setup) leaks).decodeProfile
        (initialLaw setup) horizon scheduler (profileOf site option)) state).support,
      next ∈ keep site key
  close : ∀ site, relevant site → ∀ key, lateKey setup leaks who site.1 = some key → ∀ option,
    ∀ state ∈ keep site key, PMF.WithinTV δ
      (((application setup leaks).controlStep (initialLaw setup) horizon scheduler
        ((bounds.onePacketMenu (runtime setup) leaks).decodeProfile (initialLaw setup) horizon
          scheduler (profileOf site option)) state).map (image key))
      (kernel key option (image key state))
  failure_eq : ∀ site, relevant site → ∀ key, ∀ state ∈ keep site key,
    (if failedState key state then (1 : ℝ) else 0) = failure key (image key state)

open Classical in
/-- **Failure from lumping at a kept history.** Under one-step lumping at
relevant sites, the failure probability of an option's profile over `fuel`
steps from a history whose state is kept for a relevant site and its key is
within `fuel * δ` of the failure expectation of `fuel` steps of the image kernel
from the history's image. -/
theorem PendingLumpingOn.abs_failure_sub_le_of_keep {assessment : (onePacketInformation setup
      leaks bounds horizon scheduler).BehavioralAssessment} {who : Player}
    {relevant : (onePacketInformation setup leaks bounds horizon scheduler).InformationSite who →
      Prop} {LateOption : Type}
    {profileOf : (onePacketInformation setup leaks bounds horizon scheduler).InformationSite who →
      LateOption → ∀ player,
        (onePacketInformation setup leaks bounds horizon scheduler).BehavioralPolicy player}
    {failedState : LateKey setup leaks → (application setup leaks).ProtocolState → Prop} {δ : ℝ}
    {Y : Type}
    (lumping : PendingLumpingOn assessment who relevant profileOf failedState δ Y) (fuel : Nat)
    (site : (onePacketInformation setup leaks bounds horizon scheduler).InformationSite who)
    (isRelevant : relevant site)
    (key : LateKey setup leaks) (siteKey : lateKey setup leaks who site.1 = some key)
    (option : LateOption)
    (history : (onePacketProtocol setup leaks bounds horizon scheduler).History)
    (kept : history.state ∈ lumping.keep site key) :
    |expect ((onePacketInformation setup leaks bounds horizon scheduler).runBehavioralFrom
        (profileOf site option) fuel history)
        (fun final => if failedState key final.state then 1 else 0) -
      expect ((fun law => law.bind (lumping.kernel key option))^[fuel]
        (PMF.pure (lumping.image key history.state))) (lumping.failure key)| ≤ fuel * δ := by
  have lumped := (bounds.onePacketMenu (runtime setup) leaks).run_map_withinTV (initialLaw setup)
    horizon scheduler (profileOf site option) (lumping.image key) (lumping.kernel key option)
    (lumping.keep site key) δ (lumping.kept site isRelevant key siteKey option)
    (lumping.close site isRelevant key siteKey option) fuel history kept
  have tested := lumped.abs_expect_sub_le_interval (lumping.failure key) 0 1
    (fun point _ => by simpa only [zero_add] using lumping.failure_unit key point)
  have lumped := by simpa only [mul_one] using tested
  rw [expect_map] at lumped
  have sameFailure : expect ((onePacketInformation setup leaks bounds horizon
      scheduler).runBehavioralFrom (profileOf site option) fuel history)
        (fun final => if failedState key final.state then 1 else 0) =
      expect ((onePacketInformation setup leaks bounds horizon scheduler).runBehavioralFrom
        (profileOf site option) fuel history)
        (lumping.failure key ∘ fun final => lumping.image key final.state) := by
    apply expect_congr_on_support
    intro final reached
    have stateLaw := (bounds.onePacketMenu (runtime setup) leaks).run_map_controlSteps
      (initialLaw setup) horizon scheduler (profileOf site option) fuel history
    have inside := (iterate_bind_map_withinTV _ (lumping.image key) (lumping.kernel key option)
      (lumping.keep site key) δ (lumping.kept site isRelevant key siteKey option)
      (lumping.close site isRelevant key siteKey option) fuel history.state kept).1
    have stateReached : final.state ∈ (((onePacketInformation setup leaks bounds horizon
        scheduler).runBehavioralFrom (profileOf site option) fuel history).map
          ExecutionProtocol.History.state).support := by
      rw [PMF.support_map]
      exact ⟨final, reached, rfl⟩
    rw [stateLaw] at stateReached
    exact lumping.failure_eq site isRelevant key final.state (inside final.state stateReached)
  rw [sameFailure]
  exact lumped

open Classical in
/-- **Pathwise failure from lumping at relevant sites.** Under one-step lumping
at relevant sites, the failure probability of each option from each forced
history of a relevant site with key `key`, over `fuel` steps, is within
`fuel * δ` of the failure expectation of `fuel` steps of the image kernel from
the image read off the history's operational record. -/
theorem PendingLumpingOn.pathwise {assessment : (onePacketInformation setup leaks bounds horizon
      scheduler).BehavioralAssessment} {who : Player}
    {relevant : (onePacketInformation setup leaks bounds horizon scheduler).InformationSite who →
      Prop} {LateOption : Type}
    {profileOf : (onePacketInformation setup leaks bounds horizon scheduler).InformationSite who →
      LateOption → ∀ player,
        (onePacketInformation setup leaks bounds horizon scheduler).BehavioralPolicy player}
    {failedState : LateKey setup leaks → (application setup leaks).ProtocolState → Prop} {δ : ℝ}
    {Y : Type}
    (lumping : PendingLumpingOn assessment who relevant profileOf failedState δ Y) (fuel : Nat)
    (site : (onePacketInformation setup leaks bounds horizon scheduler).InformationSite who)
    (isRelevant : relevant site)
    (key : LateKey setup leaks) (siteKey : lateKey setup leaks who site.1 = some key)
    (option : LateOption)
    (history : (onePacketInformation setup leaks bounds horizon scheduler).InformationHistory who
      site.1)
    (supported : history ∈ (assessment.belief who site).support)
    (forced : ForcedState setup leaks who history.1.state) :
    |expect ((onePacketInformation setup leaks bounds horizon scheduler).runBehavioralFrom
        (profileOf site option) fuel history.1)
        (fun final => if failedState key final.state then 1 else 0) -
      expect ((fun law => law.bind (lumping.kernel key option))^[fuel]
        (PMF.pure (lumping.start key (operationalRecord setup leaks bounds horizon scheduler
          history.1.trace)))) (lumping.failure key)| ≤ fuel * δ := by
  have bound := lumping.abs_failure_sub_le_of_keep fuel site isRelevant key siteKey option
    history.1 (lumping.start_kept site isRelevant key siteKey history supported forced)
  rwa [lumping.start_eq site isRelevant key siteKey history supported forced] at bound

/-- **The one-step lumping at late decisions, at relevant sites.** For the
owner `who`, a profile installing each option at each site, and a set of
allowed states per site that contains the forced histories of every relevant
site and is kept by the control step of its installed profiles, if at every
relevant site the owner's step at a publication turn is within `δ` of a kernel
of the key, the option and the operational state, and its law of moves at a
binding turn is within `δBinding ≤ δ / 2` of a keyed law, both at allowed
states, the native kernel lumps onto the decision image at the relevant sites,
with failure the failed completion of the decided event. -/
def onePacketLateLumpingOn
    (assessment : (onePacketInformation setup leaks bounds horizon
      scheduler).BehavioralAssessment) (who : Player)
    (relevant : (onePacketInformation setup leaks bounds horizon scheduler).InformationSite who →
      Prop) {LateOption : Type}
    (profileOf : (onePacketInformation setup leaks bounds horizon scheduler).InformationSite who →
      LateOption → ∀ player,
        (onePacketInformation setup leaks bounds horizon scheduler).BehavioralPolicy player)
    {δ δBinding : ℝ} (nonneg : 0 ≤ δ) (bindingNonneg : 0 ≤ δBinding)
    (bindingLe : 2 * δBinding ≤ δ)
    (ownerKernel : LateKey setup leaks → LateOption → Option (OperationalState setup leaks) →
      PMF (PendingImage (setup := setup) (leaks := leaks)))
    (moves : LateKey setup leaks → LateOption →
      Option (OperationalState setup leaks) × List (MessageId Player × Bool) →
        PMF (Option (Handle (graph setup))))
    (allowed : (onePacketInformation setup leaks bounds horizon scheduler).InformationSite who →
      (application setup leaks).ProtocolState → Prop)
    (allowedStart : ∀ site, relevant site → ∀ key, lateKey setup leaks who site.1 = some key →
      ∀ history ∈ (assessment.belief who site).support,
        ForcedState setup leaks who history.1.state → allowed site history.1.state)
    (allowedStep : ∀ site, relevant site → ∀ option state, allowed site state →
      ∀ next ∈ ((application setup leaks).controlStep (initialLaw setup) horizon scheduler
        ((bounds.onePacketMenu (runtime setup) leaks).decodeProfile (initialLaw setup) horizon
          scheduler (profileOf site option)) state).support, allowed site next)
    (owner : ∀ site, relevant site → ∀ key, lateKey setup leaks who site.1 = some key →
      ∀ option, OwnerStepClose ownerKernel key option (profileOf site option) δ (allowed site))
    (law : ∀ site, relevant site → ∀ key, lateKey setup leaks who site.1 = some key → ∀ option,
      OwnerBindingLaw bounds horizon scheduler moves key option (profileOf site option)
        δBinding (allowed site)) :
    PendingLumpingOn assessment who relevant profileOf DecisionFailed δ
      (DecisionImage (setup := setup) (leaks := leaks)) where
  image := decisionImage
  kernel := decisionKernel bounds horizon scheduler ownerKernel moves
  start := decisionRecordImage
  keep site key := {state | state ∈ decisionKept bounds horizon scheduler key ∧
    allowed site state}
  failure _ := decisionFailure
  failure_unit _ image := by
    rcases image with pending | binding
    · rcases pending with _ | failed
      · simp only [decisionFailure, imageFailure, le_refl, zero_le_one, and_self]
      · cases failed <;> simp only [decisionFailure, imageFailure, Bool.false_eq_true,
          ↓reduceIte, le_refl, zero_le_one, and_self]
    · rcases binding with _ | failed
      · simp only [decisionFailure, le_refl, zero_le_one, and_self]
      · cases failed <;> simp only [decisionFailure, Bool.false_eq_true, ↓reduceIte, le_refl,
          zero_le_one, and_self]
  start_eq _ _ _ siteKey history _ forced := decisionImage_of_history siteKey history forced
  start_kept site isRelevant key siteKey history supported forced :=
    ⟨decisionKept_of_history siteKey history forced,
      allowedStart site isRelevant key siteKey history supported forced⟩
  kept site isRelevant key _ option _ kept _ member :=
    ⟨decisionKept_step key (profileOf site option) kept.1 member,
      allowedStep site isRelevant option _ kept.2 _ member⟩
  close site isRelevant key siteKey option _ kept := decisionKernel_close ownerKernel moves key
    option (profileOf site option) nonneg bindingNonneg bindingLe
    (owner site isRelevant key siteKey option) (law site isRelevant key siteKey option) kept.1
    kept.2
  failure_eq _ _ key _ kept := decisionFailed_eq key kept.1

end Vegas
