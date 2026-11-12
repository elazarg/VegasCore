module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.EventGraph.LastErasedLaw
public import Vegas.EventGraph.NormalizedRestriction

@[expose] public section

/-! # Targets read from the order-free key

The last-served erased-key law of a ready independent profile is read from the
order-free key, and so is every player's normalized observation. Both are
therefore functions of the key alone: `keyTarget` and `keyView`.

A deviation from a base profile is normalized: `lastDeviationProfile` reads
the deviator's policy and every other policy through rank-normalized
observations. Patching the deviator's policy at one event changes no action law
elsewhere, and at that event the deviator plays its head on its normalized
observation.
-/

noncomputable section

namespace Vegas.EventGraph

open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

variable (graph) in
/-- The order-free key of a configuration: its cut, store and completion records. -/
abbrev RunKey :=
  graph.order.Cut × (Store graph.layout × (graph.EventId → Option graph.Completion))

/-- The last-served erased-key law from any configuration with a given key. -/
def keyTarget (profile : graph.BehavioralProfile) (who : Player) (key : RunKey graph) :
    PMF (RunKey graph) :=
  open scoped Classical in
  if found : ∃ config : graph.Config, runKey config = key then
    lastErasedLaw profile who found.choose
  else PMF.pure key

theorem keyTarget_runKey {profile : graph.BehavioralProfile} {who : Player}
    (independent : LastIndependent profile who) (config : graph.Config) :
    keyTarget profile who (runKey config) = lastErasedLaw profile who config := by
  have found : ∃ other : graph.Config, runKey other = runKey config := ⟨config, rfl⟩
  unfold keyTarget
  rw [dite_eq_left found]
  exact independent.lastErasedLaw_congr (erasedKey_congr found.choose_spec)

/-- A player's normalized observation of any configuration with a given key. -/
def keyView (who : Player) (key : RunKey graph) : Option (graph.PlayerObservation who) :=
  open scoped Classical in
  if found : ∃ config : graph.Config, runKey config = key then
    some (graph.normalizeObservation who (graph.playerObserve who found.choose))
  else none

theorem keyView_runKey (who : Player) (config : graph.Config) :
    keyView who (runKey config) =
      some (graph.normalizeObservation who (graph.playerObserve who config)) := by
  have found : ∃ other : graph.Config, runKey other = runKey config := ⟨config, rfl⟩
  unfold keyView
  rw [dite_eq_left found]
  exact congrArg some (normalizeObservation_playerObserve_congr who
    (congrArg Prod.snd found.choose_spec))

variable (graph) in
/-- The normalized deviation of `who` from a base profile. -/
def lastDeviationProfile (base : graph.BehavioralProfile) (who : Player)
    (policy : graph.BehavioralPolicy who) : graph.BehavioralProfile :=
  graph.normalizeProfile (Profile.update (sig := graph.gameSignature) base who policy)

/-- At an event of an active deviator, the deviation plays its policy on the
normalized observation. -/
theorem actionLaw_lastDeviationProfile_owned (base : graph.BehavioralProfile) (who : Player)
    (policy : graph.BehavioralPolicy who) (config : graph.Config) {event : graph.EventId}
    (owned : (graph.nodes event).actor = some who) (active : who ∉ config.defaulted) :
    actionLaw (graph.lastDeviationProfile base who policy) config event =
      policy event owned (graph.normalizeObservation who (graph.playerObserve who config))
        (fun normalized => active (graph.normalizeObservation_defaulted_subset who
          (graph.playerObserve who config) normalized)) := by
  rw [actionLaw_of_actor _ _ owned, dite_eq_right active]
  simp only [lastDeviationProfile, normalizeProfile, normalizePolicy, Profile.update_same]

/-- At events of other players, the deviation plays the normalized base. -/
theorem actionLaw_lastDeviationProfile_other (base : graph.BehavioralProfile) (who : Player)
    (policy : graph.BehavioralPolicy who) (config : graph.Config) {event : graph.EventId}
    (foreign : (graph.nodes event).actor ≠ some who) :
    actionLaw (graph.lastDeviationProfile base who policy) config event =
      actionLaw (graph.normalizeProfile base) config event := by
  cases ownerEq : (graph.nodes event).actor with
  | none => rw [actionLaw_of_ownerless _ _ ownerEq, actionLaw_of_ownerless _ _ ownerEq]
  | some owner =>
      have different : owner ≠ who := fun same => foreign (by rw [ownerEq, same])
      rw [actionLaw_of_actor _ _ ownerEq, actionLaw_of_actor _ _ ownerEq]
      by_cases inactive : owner ∈ config.defaulted
      · rw [dite_eq_left inactive, dite_eq_left inactive]
      · rw [dite_eq_right inactive, dite_eq_right inactive]
        simp only [lastDeviationProfile, normalizeProfile, normalizePolicy,
          Profile.update_of_ne _ _ different]

/-- Away from the patched event, a patched deviation has the tail's action laws. -/
theorem actionLaw_lastDeviationProfile_patch_of_ne (base : graph.BehavioralProfile)
    (who : Player) (event : graph.EventId) (head tail : graph.BehavioralPolicy who)
    (config : graph.Config) {other : graph.EventId} (different : other ≠ event) :
    actionLaw (graph.lastDeviationProfile base who (patchPolicy event head tail)) config other =
      actionLaw (graph.lastDeviationProfile base who tail) config other := by
  by_cases owned : (graph.nodes other).actor = some who
  · by_cases inactive : who ∈ config.defaulted
    · rw [actionLaw_of_actor _ _ owned, actionLaw_of_actor _ _ owned, dite_eq_left inactive,
        dite_eq_left inactive]
    · rw [actionLaw_lastDeviationProfile_owned base who _ config owned inactive,
        actionLaw_lastDeviationProfile_owned base who _ config owned inactive]
      simp only [patchPolicy, different, ↓reduceIte]
  · rw [actionLaw_lastDeviationProfile_other base who _ config owned,
      actionLaw_lastDeviationProfile_other base who _ config owned]

/-- A normalized deviation from a base whose other players ignore their
observations at publications is ready independent away from the deviator. -/
theorem RevealsOnlyConcurrent.lastIndependent_lastDeviationProfile
    (only : graph.RevealsOnlyConcurrent) (base : graph.BehavioralProfile) (who : Player)
    (oblivious : ∀ owner, owner ≠ who → ∀ event (actor : graph.actor? event = some owner),
      (graph.outputLayout event).IsPublication →
        ∀ (left right : graph.PlayerObservation owner) leftActive rightActive,
          base owner event actor left leftActive = base owner event actor right rightActive)
    (policy : graph.BehavioralPolicy who) :
    LastIndependent (graph.lastDeviationProfile base who policy) who :=
  only.lastIndependent_normalizeProfile _ who fun owner different event actor publication
      left right leftActive rightActive => by
    simp only [Profile.update_of_ne _ _ different]
    exact oblivious owner different event actor publication left right leftActive rightActive

/-- The only enabled event is the one the last scheduler picks. -/
theorem lastPick_eq_of_alone (who : Player) (config : graph.Config) {event : graph.EventId}
    (alone : ∀ other, config.cut.Ready other → other = event)
    (nonempty : config.cut.enabled.Nonempty) :
    event = graph.lastPick who config.cut.enabled nonempty :=
  (alone _ ((EventOrder.Cut.mem_enabled _ _).mp (graph.lastPick_mem who _ nonempty))).symm

end Vegas.EventGraph
