/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketKeyedRecords
import Interaction.ReactiveLumping

/-! # Pathwise late-delivery failure from lumping

The failure probability of a late-delivery option from a history is the
probability that play from that history, under the profile that installs the
option, ends in a state the key marks failed. If, while the event is pending
and after it completes, the control step of that profile read through an image
of protocol states chosen for the key is within `δ` on unit payoffs of an image kernel that depends
only on the late-delivery key and the option, if the image of a forced
history's state is read off its operational record, and if failure is a unit
function of the image, then the failure probability from each forced history
is within `fuel * δ` of a function of the key, the option and the operational
record (`Vegas.PendingLumping.pathwise`). This is the `pathwise` field of
`Vegas.LateDeliveryBlindness`, reduced to one step of the native kernel.
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
/-- **One-step lumping at late-delivery sites.** For the owner `who`, a profile
installing each option at each site, and for each key an image of protocol
states and a failure set:

* the image of a forced history's state at a site with key `key` is read off
  its operational record by `start`, and that state is kept for `key`;
* the control step of each installed profile keeps the kept states for `key`,
  and read through the key's image it is within `δ` on unit payoffs of the
  image kernel of `key` and the option;
* failure of a kept state is a unit function of its image. -/
structure PendingLumping (assessment : (onePacketInformation setup leaks bounds horizon
      scheduler).BehavioralAssessment) (who : Player) {LateOption : Type}
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
  /-- The kept states for a key. -/
  keep : LateKey setup leaks → Set (application setup leaks).ProtocolState
  /-- Failure as a function of the image. -/
  failure : LateKey setup leaks → Y → ℝ
  failure_unit : ∀ key y, 0 ≤ failure key y ∧ failure key y ≤ 1
  start_eq : ∀ site key, lateKey setup leaks who site.1 = some key →
    ∀ history ∈ (assessment.belief who site).support,
      ForcedState setup leaks who history.1.state →
        image key history.1.state =
          start key (operationalRecord setup leaks bounds horizon scheduler history.1.trace)
  start_kept : ∀ site key, lateKey setup leaks who site.1 = some key →
    ∀ history ∈ (assessment.belief who site).support,
      ForcedState setup leaks who history.1.state → history.1.state ∈ keep key
  kept : ∀ site key, lateKey setup leaks who site.1 = some key → ∀ option,
    ∀ state ∈ keep key, ∀ next ∈ ((application setup leaks).controlStep (initialLaw setup)
      horizon scheduler ((bounds.onePacketMenu (runtime setup) leaks).decodeProfile
        (initialLaw setup) horizon scheduler (profileOf site option)) state).support,
      next ∈ keep key
  close : ∀ site key, lateKey setup leaks who site.1 = some key → ∀ option,
    ∀ state ∈ keep key, UnitClose δ
      (((application setup leaks).controlStep (initialLaw setup) horizon scheduler
        ((bounds.onePacketMenu (runtime setup) leaks).decodeProfile (initialLaw setup) horizon
          scheduler (profileOf site option)) state).map (image key))
      (kernel key option (image key state))
  failure_eq : ∀ key, ∀ state ∈ keep key,
    (if failedState key state then (1 : ℝ) else 0) = failure key (image key state)

open Classical in
/-- **Pathwise failure from lumping.** Under one-step lumping, the failure
probability of each option from each forced history of a site with key `key`,
over `fuel` steps, is within `fuel * δ` of the failure expectation of `fuel`
steps of the image kernel from the image read off the history's operational
record. -/
theorem PendingLumping.pathwise {assessment : (onePacketInformation setup leaks bounds horizon
      scheduler).BehavioralAssessment} {who : Player} {LateOption : Type}
    {profileOf : (onePacketInformation setup leaks bounds horizon scheduler).InformationSite who →
      LateOption → ∀ player,
        (onePacketInformation setup leaks bounds horizon scheduler).BehavioralPolicy player}
    {failedState : LateKey setup leaks → (application setup leaks).ProtocolState → Prop} {δ : ℝ}
    {Y : Type}
    (lumping : PendingLumping assessment who profileOf failedState δ Y) (fuel : Nat)
    (site : (onePacketInformation setup leaks bounds horizon scheduler).InformationSite who)
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
  have lumped := (bounds.onePacketMenu (runtime setup) leaks).run_map_unitClose (initialLaw setup)
    horizon scheduler (profileOf site option) (lumping.image key) (lumping.kernel key option)
    (lumping.keep key) δ (lumping.kept site key siteKey option)
    (lumping.close site key siteKey option) fuel history.1
    (lumping.start_kept site key siteKey history supported forced) (lumping.failure key)
    (lumping.failure_unit key)
  rw [lumping.start_eq site key siteKey history supported forced, expect_map] at lumped
  have sameFailure : expect ((onePacketInformation setup leaks bounds horizon
      scheduler).runBehavioralFrom (profileOf site option) fuel history.1)
        (fun final => if failedState key final.state then 1 else 0) =
      expect ((onePacketInformation setup leaks bounds horizon scheduler).runBehavioralFrom
        (profileOf site option) fuel history.1)
        (lumping.failure key ∘ fun final => lumping.image key final.state) := by
    apply expect_congr_on_support
    intro final reached
    have stateLaw := (bounds.onePacketMenu (runtime setup) leaks).run_map_controlSteps
      (initialLaw setup) horizon scheduler (profileOf site option) fuel history.1
    have inside := (iterate_bind_map_unitClose _ (lumping.image key) (lumping.kernel key option)
      (lumping.keep key) δ (lumping.kept site key siteKey option)
      (lumping.close site key siteKey option) fuel history.1.state
      (lumping.start_kept site key siteKey history supported forced)).1
    have stateReached : final.state ∈ (((onePacketInformation setup leaks bounds horizon
        scheduler).runBehavioralFrom (profileOf site option) fuel history.1).map
          ExecutionProtocol.History.state).support := by
      rw [PMF.support_map]
      exact ⟨final, reached, rfl⟩
    rw [stateLaw] at stateReached
    exact lumping.failure_eq key final.state (inside final.state stateReached)
  rw [sameFailure]
  exact lumped

end Vegas
