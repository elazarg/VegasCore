/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceRosterPolicy

/-! # Retained responses in a finite revelation roster

This finite menu uses the existing effective response bound. It retains all known
envelope replays, including a pending canonical opening, and permits one fresh
canonical opening per phase. Its stopping test reads the player's actual own
response recall. The full target menu still permits every bounded raw response.

This defines an ordinary action restriction, not an equilibrium claim. Source
value coverage, all-history phase invariants and the common fully mixed policy
sequence must establish the source-to-restricted-runtime correspondence.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

open Classical in
def rosterFresh? (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player) (who : Player)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) : Option (application setup leaks).Action := do
  let event ← view.application.publicView.serviceGrant
  if (graph setup).actor? event ≠ some who then none else
    let (candidate, raw) ← rosterOpening? setup leaks who event view
    let opening := (runtime setup).windowOpening leaks event candidate raw
    if ((past.drop (rosterOffset setup rosters who event)).any
        fun entry => entry.action = opening) then none else some opening

theorem rosterFresh?_shape (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player) (who : Player)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (action : (application setup leaks).Action)
    (found : rosterFresh? setup leaks rosters who past view = some action) :
    ∃ event candidate raw,
      view.application.publicView.serviceGrant = some event ∧
      (graph setup).actor? event = some who ∧
      rosterOpening? setup leaks who event view = some (candidate, raw) ∧
      action = (runtime setup).windowOpening leaks event candidate raw ∧
      ∀ entry ∈ past.drop (rosterOffset setup rosters who event), entry.action ≠ action := by
  classical
  unfold rosterFresh? at found
  obtain ⟨event, granted, found⟩ := Option.bind_eq_some_iff.mp found
  split at found
  · cases found
  · rename_i owned
    obtain ⟨⟨candidate, raw⟩, opening, found⟩ := Option.bind_eq_some_iff.mp found
    dsimp only at found
    by_cases fresh : ((past.drop (rosterOffset setup rosters who event)).any
        fun entry => decide (entry.action =
          (runtime setup).windowOpening leaks event candidate raw)) = true
    · rw [ite_eq_left fresh] at found
      cases found
    · rw [ite_eq_right fresh] at found
      have same := Option.some.inj found
      refine ⟨event, candidate, raw, granted, not_not.mp owned, opening, same.symm, ?_⟩
      intro entry member equal
      apply fresh
      apply List.any_eq_true.mpr
      exact ⟨entry, member, by simpa only [same, decide_eq_true_eq] using equal⟩

variable [Fintype Player]

open Classical in
def rosterActions (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
    (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) : Finset (application setup leaks).Action :=
  ((application setup leaks).replayActions past view ∪
    (rosterFresh? setup leaks rosters who past view).toList.toFinset) ∩
      (bounds.menu (runtime setup) leaks).actions who past view

theorem silence_roster (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
    (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) :
    (⟨none⟩ : (application setup leaks).Action) ∈
      rosterActions setup leaks bounds rosters who past view := by
  classical
  refine Finset.mem_inter.mpr ⟨Finset.mem_union_left _
    (((application setup leaks).mem_replayActions_iff _ _ _).mpr ?_), ?_⟩
  · exact (application setup leaks).replayPolicy_support past view none
      (Finset.mem_insert_self _ _)
  · rw [bounds.menu_mem]
    exact ⟨True.intro, rfl⟩

/-- The replay law's support is exactly lawful raw traffic, without imposing a
static bound on identifiers already known through actual recall or observation. -/
theorem replay_roster (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
    (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (action : (application setup leaks).Action)
    (member : action ∈ ((application setup leaks).replayPolicy past view).support) :
    action ∈ rosterActions setup leaks bounds rosters who past view := by
  classical
  refine Finset.mem_inter.mpr ⟨Finset.mem_union_left _
    (((application setup leaks).mem_replayActions_iff _ _ _).mpr member), ?_⟩
  obtain ⟨selected, supported, rfl⟩ := PMF.support_map .. ▸ member
  have eligible := (PMF.mem_support_uniformOfFinset_iff _ _).mp supported
  cases selected with
  | none =>
      rw [bounds.menu_mem]
      exact ⟨True.intro, rfl⟩
  | some id =>
      simp only [ReactiveApplication.replayOptions, Finset.mem_insert, Option.some_ne_none,
        false_or, Finset.mem_image, List.mem_toFinset, List.mem_map, Option.some.injEq] at eligible
      obtain ⟨key, ⟨message, known, same⟩, rfl⟩ := eligible
      exact bounds.known_replay_available (runtime setup) leaks who past view key
        ⟨message, known, same⟩

def rosterMenu (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup))
    (rosters : (graph setup).EventId → List Player) : (application setup leaks).ResponseMenu where
  actions := rosterActions setup leaks bounds rosters
  nonempty who past view := ⟨⟨none⟩, silence_roster setup leaks bounds rosters who past view⟩

theorem rosterMenu_in_effective (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player) :
    (rosterMenu setup leaks bounds rosters).IncludedIn (bounds.menu (runtime setup) leaks) := by
  classical
  intro who past view
  exact Finset.inter_subset_right

theorem rosterMenu_in_raw (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player) :
    (rosterMenu setup leaks bounds rosters).IncludedIn (bounds.rawMenu (runtime setup) leaks) := by
  intro who past view action member
  obtain ⟨original, allowed, normal⟩ := ((runtime setup).reactiveNormalization leaks).menu_mem
    (bounds.rawMenu (runtime setup) leaks) who past view action |>.mp
      (rosterMenu_in_effective setup leaks bounds rosters who past view member)
  rw [← normal]
  exact bounds.rawMenu_closed (runtime setup) leaks who past view original allowed

theorem roster_response_cases (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
    (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (action : (application setup leaks).Action)
    (member : action ∈ rosterActions setup leaks bounds rosters who past view) :
    action ∈ ((application setup leaks).replayPolicy past view).support ∨
      rosterFresh? setup leaks rosters who past view = some action := by
  classical
  rcases Finset.mem_union.mp (Finset.mem_inter.mp member).1 with waiting | opening
  · exact Or.inl (((application setup leaks).mem_replayActions_iff _ _ _).mp waiting)
  · exact Or.inr (by simpa only [List.mem_toFinset, Option.mem_toList] using opening)

omit [Fintype Player] in
/-- The explicit limiting policy stops after an earlier disclosure at every
input, including histories with zero limiting probability. -/
theorem rosterLimitPolicy_cases (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (profile : BehavioralProfile setup.program) (who : Player)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (action : (application setup leaks).Action)
    (supported : action ∈ (rosterLimitPolicy setup leaks rosters profile who past view).support) :
    action ∈ ((application setup leaks).replayPolicy past view).support ∨
      rosterFresh? setup leaks rosters who past view = some action := by
  classical
  unfold rosterLimitPolicy at supported
  split at supported
  · exact Or.inl supported
  · rename_i event granted
    split at supported
    · rename_i owned
      split at supported
      · exact Or.inl supported
      · rename_i candidate raw opening
        dsimp only at supported
        split at supported
        · exact Or.inl supported
        · rename_i notStopped
          obtain ⟨disclose, _, supported⟩ :=
            Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
          cases disclose with
          | false => exact Or.inl supported
          | true =>
              cases (PMF.mem_support_pure_iff _ _).mp supported
              apply Or.inr
              unfold rosterFresh?
              rw [granted]
              dsimp only [bind, Option.bind]
              rw [ite_eq_right (not_not_intro owned), opening]
              dsimp only [bind, Option.bind]
              have absent : ¬ ((past.drop (rosterOffset setup rosters who event)).any
                  fun entry => decide (entry.action =
                    (runtime setup).windowOpening leaks event candidate raw)) = true := by
                intro present
                apply notStopped
                simp only [present, Bool.true_or]
              exact ite_eq_right absent
    · exact Or.inl supported

/-- Application constancy holds for all permitted responses, not only the
compiled policy. This is the support-level phase invariant required at
zero-probability retained histories. -/
theorem roster_response_application (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
    (who : Player) (execution : (application setup leaks).Execution)
    (action : (application setup leaks).Action)
    (member : action ∈ rosterActions setup leaks bounds rosters who
      (execution.recall who) (execution.observe (application setup leaks) who)) :
    (execution.respond (application setup leaks) who action).application =
      execution.application := by
  rcases roster_response_cases setup leaks bounds rosters who _ _ action member with waiting | fresh
  · rcases (application setup leaks).replayPolicy_cases _ _ action waiting with rfl | ⟨id, rfl⟩
    · rfl
    · rfl
  · obtain ⟨event, candidate, raw, _, _, _, rfl, _⟩ :=
      rosterFresh?_shape setup leaks rosters who _ _ action fresh
    rfl

/-- Arbitrary retained responses preserve the application throughout an
activation-only prefix, including private observation and replay branches. -/
theorem roster_run_application (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
    (players : Player → (application setup leaks).Policy)
    (covered : ∀ who past view response, response ∈ (players who past view).support →
      response ∈ rosterActions setup leaks bounds rosters who past view)
    (network : (runtime setup).NetworkPolicy leaks) (visits : List Player)
    (initial final : (application setup leaks).Execution)
    (reached : final ∈ ((runtime setup).runInteractionPlan leaks players network
      (visits.map ServiceInstruction.player) initial).support) :
    final.application = initial.application := by
  let app := application setup leaks
  induction visits generalizing initial with
  | nil =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      rfl
  | cons who rest ih =>
      simp only [List.map_cons, EventGraphRuntime.runInteractionPlan,
        EventGraphRuntime.interactionStep, EventGraphRuntime.interactionInstruction,
        PMF.pure_bind, ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
        ReactiveApplication.resume, ReactiveApplication.invoke,
        ReactiveApplication.Execution.activation_samples, PMF.bind_map,
        PMF.bind_bind, Function.comp_def] at reached
      obtain ⟨sample, _, reached⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      obtain ⟨action, supported, reached⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      exact (ih _ reached).trans
        (roster_response_application setup leaks bounds rosters who
          (initial.sampledActivation app who sample) action (covered who _ _ action supported))

end Vegas
