/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.RevealSequence
import Vegas.Compile.EventGraphInputs
import Vegas.Compile.EventGraphPolicy
import Vegas.EventGraph.Sequential
import Vegas.Pending.ReactiveRevealBlock
import Vegas.Pending.ReactiveMonitoring
import Vegas.Pending.ReactiveFiniteResponses
import Interaction.ReactiveResponseMenu
import Interaction.ReactiveMenuRestriction

/-! # Restricted native service for source revelation sequences

These are constructor functions for the existing event graph, reactive service,
and response menu. The first backend has one ordinary owner activation and one
watcher activation per source event. It therefore has a fixed finite calendar;
it does not model arbitrarily many intervening broadcasts.

Canonical openings are included before the watcher observes pending packets.
Withholding is silence, or replay of an already published envelope, followed by
expiry. These replays retain the player's own response recall; their source
interpretation requires action splitting, not erasing native histories.
Deadlines increase with source rank
so that a successor can remain timely after an early successful predecessor.
The definitions assert no equilibrium property; operational timeliness and the
source-history correspondence are proved in the modules that use them.
-/

noncomputable section

namespace Vegas

open SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

theorem eventCount_eq_instructionCount {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) : eventCount program = instructionCount program := by
  induction program with
  | ret payoffs => rfl
  | sample name fresh law next ih => exact congrArg Nat.succ ih
  | commit name owner fresh guard next ih => exact congrArg Nat.succ ih
  | reveal published owner name fresh source unresolved next ih => exact congrArg Nat.succ ih

/-- Source rank retains the actual owner, including when an owner recurs. -/
theorem RevealOnly.event_owner {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (reveals : program.RevealOnly)
    (event : Fin (eventCount program)) : ∃ owner, eventOwner? program event = some owner := by
  induction program with
  | ret payoffs => exact Fin.elim0 event
  | sample name fresh law next ih => exact reveals.elim
  | commit name owner fresh guard next ih => exact reveals.elim
  | reveal published owner name fresh source unresolved next ih =>
      exact Fin.cases ⟨owner, rfl⟩ (fun later => ih reveals later) event

end Vegas

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

abbrev graph (setup : Setup (Player := Player) (L := L)) := setup.eventGraph.sequentialize

def runtime (setup : Setup (Player := Player) (L := L)) : EventGraphRuntime (graph setup) where
  deadline event := event.val + 1

theorem runtime_deadline_pos (setup : Setup (Player := Player) (L := L))
    (event : (graph setup).EventId) : 0 < (runtime setup).deadline event := Nat.zero_lt_succ _

theorem runtime_deadline_increases (setup : Setup (Player := Player) (L := L))
    (first second : (graph setup).EventId) (before : first.val < second.val) :
    (runtime setup).deadline first < (runtime setup).deadline second := by
  change first.val + 1 < second.val + 1
  omega

theorem source_owner (setup : Setup (Player := Player) (L := L))
    (reveals : setup.program.RevealOnly) (event : (graph setup).EventId) :
    ∃ owner, (graph setup).actor? event = some owner := by
  obtain ⟨owner, owned⟩ := Vegas.RevealOnly.event_owner setup.program reveals event
  refine ⟨owner, ?_⟩
  change (toEventGraph setup.program).actor? event = some owner
  rw [← eventOwner?_eq_actor, owned]

def block (setup : Setup (Player := Player) (L := L)) (watcher : Player)
    (event : (graph setup).EventId) : List (ServiceInstruction (graph setup)) :=
  [.grant event] ++ (match (graph setup).actor? event with
    | none => []
    | some owner => [.player owner, .includeLatest event owner]) ++
    [.player watcher, .wire] ++ List.replicate ((runtime setup).deadline event) .tick ++
    [.expire event]

def plan (setup : Setup (Player := Player) (L := L)) (watcher : Player) :
    List (ServiceInstruction (graph setup)) :=
  (List.finRange (graph setup).order.eventCount).flatMap (block setup watcher)

theorem block_of_owner (setup : Setup (Player := Player) (L := L)) (watcher owner : Player)
    (event : (graph setup).EventId) (owned : (graph setup).actor? event = some owner) :
    block setup watcher event =
      [.grant event, .player owner, .includeLatest event owner, .player watcher, .wire] ++
        List.replicate (event.val + 1) .tick ++ [.expire event] := by
  simp only [block, owned, List.cons_append, List.nil_append, runtime]

theorem block_length (setup : Setup (Player := Player) (L := L)) (watcher : Player)
    (reveals : setup.program.RevealOnly) (event : (graph setup).EventId) :
    (block setup watcher event).length = event.val + 7 := by
  obtain ⟨owner, owned⟩ := source_owner setup reveals event
  rw [block_of_owner setup watcher owner event owned]
  simp only [List.length_append, List.length_cons, List.length_nil, List.length_replicate]
  omega

theorem plan_grant_order (setup : Setup (Player := Player) (L := L)) (watcher : Player) :
    (plan setup watcher).filterMap (fun instruction => match instruction with
      | .grant event => some event
      | _ => none) = List.finRange (graph setup).order.eventCount := by
  have each (event : (graph setup).EventId) :
      (block setup watcher event).filterMap (fun instruction => match instruction with
        | .grant selected => some selected
        | _ => none) = [event] := by
    unfold block
    cases (graph setup).actor? event <;> simp
  simp only [plan, List.filterMap_flatMap, each]
  rw [← List.map_eq_flatMap]
  exact List.map_id _

theorem plan_expiry_order (setup : Setup (Player := Player) (L := L)) (watcher : Player) :
    (plan setup watcher).filterMap (fun instruction => match instruction with
      | .expire event => some event
      | _ => none) = List.finRange (graph setup).order.eventCount := by
  have each (event : (graph setup).EventId) :
      (block setup watcher event).filterMap (fun instruction => match instruction with
        | .expire selected => some selected
        | _ => none) = [event] := by
    unfold block
    cases (graph setup).actor? event <;> simp
  simp only [plan, List.filterMap_flatMap, each]
  rw [← List.map_eq_flatMap]
  exact List.map_id _

variable (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

abbrev application := (runtime setup).reactiveApplication leaks

def initialLaw : PMF (EventGraphRuntime.State (graph setup)) :=
  setup.initialLaw.map (fun initial => EventGraphRuntime.State.initial (setup.eventInputs initial))

/-- The fixed service consults only its own public command recall and the
existing public report selector. Private sampling remains the given rule. -/
def scheduler (watcher : Player) : (application setup leaks).Scheduler := fun history view =>
  match (plan setup watcher)[history.length]? with
  | none => PMF.pure .wait
  | some instruction => (runtime setup).interactionInstruction leaks
      ((runtime setup).reportNetwork leaks watcher) history view instruction

/-- With a finitely supported prior and a finitely branching leak rule, all of
the fixed service's nature branches finitely: its own instructions are
deterministic. -/
instance scheduler_finiteNature [setup.FiniteInitialLaw] [leaks.FiniteSupport]
    (watcher : Player) :
    (application setup leaks).FiniteNature (initialLaw setup) (scheduler setup leaks watcher) where
  initial_finite := by
    rw [initialLaw, PMF.support_map]
    exact setup.initialLaw_support_finite.image _
  scheduler_finite history view := by
    unfold scheduler
    split
    · simp
    · rename_i instruction _
      cases instruction with
      | wire => simp [(runtime setup).reportNetwork_instruction leaks watcher history view]
      | _ => simp [EventGraphRuntime.interactionInstruction]

abbrev horizon (watcher : Player) : Nat := (plan setup watcher).length

/-- A local view determines the sole canonical opening, when the granted event
is an owned, successfully openable resolution. No private global state is read. -/
def opening? (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) : Option (application setup leaks).Action := do
  let event ← view.application.publicView.serviceGrant
  if (graph setup).actor? event ≠ some who then none else
    match nodeView (graph setup) event with
    | .sample .. | .bind .. => none
    | .resolve _ payload binding checks _ _ =>
        match EventGraph.EventCode.resolveOutput? binding checks true
            view.application.observation.store with
        | none | some .failure => none
        | some (.success value) => do
            let candidate ← view.application.publicView.accepted binding.field
            if candidate.1 ≠ who then none else
              some (((runtime setup).reactiveNormalization leaks).action who past view
                ((runtime setup).canonicalRevealResponse leaks event candidate
                  ⟨payload, value⟩ true))

variable [Fintype Player] (bounds : MessageBounds (graph setup))

theorem silence_effective (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) :
    (⟨none⟩ : (application setup leaks).Action) ∈
      (bounds.menu (runtime setup) leaks).actions who past view := by
  rw [bounds.menu_mem]
  exact ⟨trivial, rfl⟩

open Classical in
def publishedReplays (view : (application setup leaks).PlayerView) :
    Finset (application setup leaks).Action :=
  (view.messages.ledger.map (fun message =>
    (⟨some (.replay message.id)⟩ : (application setup leaks).Action))).toFinset

omit [Fintype Player] in
theorem mem_publishedReplays (view : (application setup leaks).PlayerView)
    (response : (application setup leaks).Action) :
    response ∈ publishedReplays setup leaks view ↔
      ∃ message ∈ view.messages.ledger, response = ⟨some (.replay message.id)⟩ := by
  classical
  simp only [publishedReplays, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨message, member, same⟩
    exact ⟨message, member, same.symm⟩
  · rintro ⟨message, member, same⟩
    exact ⟨message, member, same.symm⟩

open Classical in
def ordinaryActions (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) : Finset (application setup leaks).Action :=
  (insert ⟨none⟩ ((opening? setup leaks who past view).toList.toFinset ∪
    publishedReplays setup leaks view)) ∩
    (bounds.menu (runtime setup) leaks).actions who past view

theorem silence_ordinary (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) :
    (⟨none⟩ : (application setup leaks).Action) ∈
      ordinaryActions setup leaks bounds who past view := by
  classical
  exact Finset.mem_inter.mpr ⟨Finset.mem_insert_self _ _,
    silence_effective setup leaks bounds who past view⟩

/-- The finite backend bound applies at every view. Source correspondence must
separately establish that its supported initial values cover every legal opening. -/
theorem ordinary_effective (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) :
    ordinaryActions setup leaks bounds who past view ⊆
      (bounds.menu (runtime setup) leaks).actions who past view := by
  classical
  exact Finset.inter_subset_right

theorem opening_ordinary (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (response : (application setup leaks).Action)
    (selected : opening? setup leaks who past view = some response)
    (covered : response ∈ (bounds.menu (runtime setup) leaks).actions who past view) :
    response ∈ ordinaryActions setup leaks bounds who past view := by
  classical
  apply Finset.mem_inter.mpr
  exact ⟨by simp [selected], covered⟩

theorem published_replay_ordinary (who : Player)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView)
    (message : Message Player (WitnessedPacket (graph setup)))
    (published : message ∈ view.messages.ledger) :
    (⟨some (.replay message.id)⟩ : (application setup leaks).Action) ∈
      ordinaryActions setup leaks bounds who past view := by
  classical
  refine Finset.mem_inter.mpr ⟨?_, ?_⟩
  · apply Finset.mem_insert_of_mem
    exact Finset.mem_union_right _
      ((mem_publishedReplays setup leaks view _).mpr ⟨message, published, rfl⟩)
  · apply bounds.known_replay_available (runtime setup) leaks who past view message.id
    exact ⟨message, List.mem_append_right _ published, rfl⟩

/-- The added aliases are exactly replays of already published envelopes. This
does not identify the player's private recall after different responses. -/
theorem ordinary_response_cases (who : Player)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (response : (application setup leaks).Action)
    (member : response ∈ ordinaryActions setup leaks bounds who past view) :
    response = ⟨none⟩ ∨ opening? setup leaks who past view = some response ∨
      ∃ message ∈ view.messages.ledger, response = ⟨some (.replay message.id)⟩ := by
  classical
  obtain silent | other := Finset.mem_insert.mp (Finset.mem_inter.mp member).1
  · exact Or.inl silent
  · rcases Finset.mem_union.mp other with opening | published
    · exact Or.inr (Or.inl (by simpa using opening))
    · exact Or.inr (Or.inr ((mem_publishedReplays setup leaks view response).mp published))

open Classical in
/-- This restricts the existing native menu to silence, a supported opening,
and published replay aliases. Source value coverage remains a proof obligation.
The watcher follows the existing reporting policy at every local input. -/
def menu (watcher : Player) : (application setup leaks).ResponseMenu where
  actions who past view := if who = watcher then
      ((application setup leaks).reportFirstUnpublished_support_finite past view).toFinset
    else ordinaryActions setup leaks bounds who past view
  nonempty who past view := by
    split
    · obtain ⟨action, supported⟩ :=
        ((application setup leaks).reportFirstUnpublished past view).support_nonempty
      exact ⟨action, (Set.Finite.mem_toFinset _).mpr supported⟩
    · exact ⟨⟨none⟩, silence_ordinary setup leaks bounds who past view⟩

theorem report_effective (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (response : (application setup leaks).Action)
    (supported : response ∈
      ((application setup leaks).reportFirstUnpublished past view).support) :
    response ∈ (bounds.menu (runtime setup) leaks).actions who past view := by
  unfold ReactiveApplication.reportFirstUnpublished at supported
  cases found : view.messages.leaked.find? (fun message =>
      decide (message.id ∉ view.messages.ledger.map Message.id)) with
  | none =>
      rw [found, PMF.mem_support_pure_iff _ _] at supported
      subst response
      exact silence_effective setup leaks bounds who past view
  | some message =>
      rw [found, PMF.mem_support_pure_iff _ _] at supported
      subst response
      apply bounds.known_replay_available (runtime setup) leaks who past view message.id
      exact ⟨message, List.mem_append_left _ (List.mem_append_right _
        (List.mem_of_find?_eq_some found)), rfl⟩

/-- The construction is literally a menu restriction of this bounded native
backend, at every local input, rather than just along compiled play. -/
theorem menu_in_effective (watcher : Player) :
    (menu setup leaks bounds watcher).IncludedIn (bounds.menu (runtime setup) leaks) := by
  intro who past view response member
  change response ∈ (if who = watcher then _ else _) at member
  split at member
  · exact report_effective setup leaks bounds who past view response
      ((Set.Finite.mem_toFinset _).mp member)
  · exact ordinary_effective setup leaks bounds who past view member

abbrev protocol (watcher : Player) :=
  (menu setup leaks bounds watcher).protocol (initialLaw setup) (horizon setup watcher)
    (scheduler setup leaks watcher)

abbrev information (watcher : Player) :=
  (menu setup leaks bounds watcher).information (initialLaw setup) (horizon setup watcher)
    (scheduler setup leaks watcher)

end Vegas
