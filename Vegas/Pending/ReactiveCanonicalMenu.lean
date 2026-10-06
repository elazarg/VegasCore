/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveCanonicalDecision

/-! # Canonical retained responses under an arbitrary scheduler

Every opportunity retains silence and one first canonical source decision.
Bindings range over the fixed typed value domain; resolutions range over
disclosure and withholding. A fresh decision is available only at its owner's
ready turn and while actual inclusion is still timely. This deadline gate is
`WithinDeadline`: a packet outside the stronger protected inclusion window can
still be accepted by an earlier inclusion.

The menu imposes no roster obligation. A player may continue to defer until
expiry, and a submitted event remains recorded even if inclusion rejects its
packet. Local coverage does not claim that retained deferrals avoid public
misses or that every retained packet is accepted at settlement.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- A canonical decision emits nothing or names exactly its decision event. -/
theorem canonicalReactiveDecision_transmission (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (event : graph.EventId) (choice : graph.Action event)
    (view : PlayerView graph) :
    (runtime.canonicalReactiveDecision leaks who event choice view).transmission = none ∨
      ∃ material,
        (runtime.canonicalReactiveDecision leaks who event choice view).transmission =
            some material ∧ material.call.packet.event? graph = some event := by
  unfold canonicalReactiveDecision
  split
  · exact Or.inl rfl
  · cases selected : canonicalFreshSlot who view with
    | none => exact Or.inl rfl
    | some serial => exact Or.inr ⟨_, rfl, rfl⟩
  · rename_i owner payload binding checks outputEq codeEq nodeEq
    cases sent : reactiveResolutionPacket who event payload binding checks outputEq choice view with
    | none => exact Or.inl (by simp only [Option.map_none])
    | some packet =>
        exact Or.inr ⟨_, by simp only [Option.map_some]; rfl,
          reactiveResolutionPacket_event who event payload binding checks outputEq choice view
            packet sent⟩

/-- A canonical decision is silent or names exactly its decision event. -/
theorem canonicalServiceDecision_cases (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (event : graph.EventId) (choice : graph.Action event) :
    runtime.canonicalServiceDecision leaks who past view event choice = ⟨none⟩ ∨
      runtime.submittedEvent? leaks
        (runtime.canonicalServiceDecision leaks who past view event choice) = some event := by
  rcases runtime.canonicalReactiveDecision_transmission leaks who event choice view.application
      with silent | ⟨material, emitted, named⟩
  · have same : runtime.canonicalReactiveDecision leaks who event choice view.application =
        ⟨none⟩ := congrArg (fun transmission =>
          (⟨transmission⟩ : (runtime.reactiveApplication leaks).Action)) silent
    left
    simpa only [canonicalServiceDecision, same] using
      (show (runtime.reactiveNormalization leaks).action who past view ⟨none⟩ = ⟨none⟩ from rfl)
  · have same : runtime.canonicalReactiveDecision leaks who event choice view.application =
        ⟨some material⟩ := congrArg (fun transmission =>
          (⟨transmission⟩ : (runtime.reactiveApplication leaks).Action)) emitted
    obtain ⟨⟨packet, opening⟩, evidence⟩ := material
    cases packet with
    | commitment other candidate | opening other candidate raw | malformed raw =>
        right
        simp only [canonicalServiceDecision, same]
        rw [runtime.submittedEvent_normalization]
        exact named

/-- Semantic normalization preserves the submitted event identity. -/
theorem canonicalServiceDecision_submittedEvent (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (event : graph.EventId) (choice : graph.Action event) :
    runtime.submittedEvent? leaks
        (runtime.canonicalServiceDecision leaks who past view event choice) = none ∨
      runtime.submittedEvent? leaks
        (runtime.canonicalServiceDecision leaks who past view event choice) = some event := by
  rcases runtime.canonicalServiceDecision_cases leaks who past view event choice with silent | named
  · rw [silent]
    exact Or.inl rfl
  · exact Or.inr named

/-- An unrecorded event's canonical decision is a first submission, including
when that decision is represented by silence. -/
theorem canonicalServiceDecision_firstSubmission (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (event : graph.EventId) (choice : graph.Action event)
    (unsent : runtime.eventRecorded leaks past event = false) :
    runtime.firstSubmission leaks past
        (runtime.canonicalServiceDecision leaks who past view event choice) = true := by
  rcases runtime.canonicalServiceDecision_submittedEvent leaks who past view event choice
    with absent | named
  · simp only [firstSubmission, absent]
  · simp only [firstSubmission, named, unsent, Bool.not_false]

namespace MessageBounds

variable (bounds : MessageBounds graph)

open Classical in
/-- The source choices represented at each constructor. Samples are supplied
by the environment and contribute no player decision. -/
def canonicalChoices (event : graph.EventId) : Finset (graph.Action event) :=
  match nodeView graph event with
  | .sample .. => ∅
  | .bind _ payload outputEq _ =>
      (bounds.typedValues payload).image fun value =>
        cast (congrArg EventField.Action outputEq.symm) (PublicationResult.success value)
  | .resolve _ _ _ _ outputEq _ =>
      Finset.univ.image fun disclose : Bool =>
        cast (congrArg EventField.Action outputEq.symm) disclose

variable [Fintype Player] (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

/-- A bounded raw canonical decision is available after normalization or
representation of withholding by silence. -/
theorem canonicalServiceDecision_available (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (event : graph.EventId) (choice : graph.Action event)
    (available : runtime.canonicalReactiveDecision leaks who event choice view.application ∈
      (bounds.rawMenu runtime leaks).actions who past view) :
    runtime.canonicalServiceDecision leaks who past view event choice ∈
      (bounds.menu runtime leaks).actions who past view := by
  unfold canonicalServiceDecision
  generalize runtime.canonicalReactiveDecision leaks who event choice view.application =
    response at available ⊢
  obtain ⟨transmission⟩ := response
  cases transmission with
  | none =>
      rw [bounds.menu_mem]
      exact ⟨trivial, rfl⟩
  | some material =>
      obtain ⟨⟨packet, opening⟩, evidence⟩ := material
      cases packet with
      | commitment other candidate | opening other candidate raw | malformed raw =>
          rw [menu, ReactiveApplication.SubmissionNormalization.menu_mem]
          exact ⟨_, available, rfl⟩

open Classical in
/-- Timely canonical decisions at the player's own ready event. The delivery
bound is deliberately absent from this acceptance gate. -/
def canonicalDecisionActions (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView) :
    Finset (runtime.reactiveApplication leaks).Action :=
  match view.application.publicView.ownTurn? who with
  | none => ∅
  | some event =>
      if graph.actor? event = some who ∧ view.application.publicView.EventReady event ∧
          view.application.publicView.WithinDeadline runtime event then
        (bounds.canonicalChoices event).image
          (runtime.canonicalServiceDecision leaks who past view event)
      else ∅

open Classical in
/-- Every opportunity retains deferral. A canonical packet may be submitted
only once, and the response must fit the bounded effective menu. -/
def canonicalActions (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView) :
    Finset (runtime.reactiveApplication leaks).Action :=
  ((bounds.canonicalDecisionActions runtime leaks who past view).filter
    (fun response => runtime.firstSubmission leaks past response) ∪ {⟨none⟩}) ∩
      (bounds.menu runtime leaks).actions who past view

theorem silence_canonical (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView) :
    (⟨none⟩ : (runtime.reactiveApplication leaks).Action) ∈
      bounds.canonicalActions runtime leaks who past view := by
  classical
  exact Finset.mem_inter.mpr
    ⟨Finset.mem_union_right _ (Finset.mem_singleton_self _),
      (bounds.menu_mem runtime leaks who past view _).mpr ⟨trivial, rfl⟩⟩

theorem silent_canonical (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (response : (runtime.reactiveApplication leaks).Action)
    (chosen : response ∈ ((runtime.reactiveApplication leaks).silentPolicy past view).support) :
    response ∈ bounds.canonicalActions runtime leaks who past view := by
  cases (runtime.reactiveApplication leaks).silentPolicy_cases past view response chosen
  exact bounds.silence_canonical runtime leaks who past view

theorem canonicalActions_nonempty (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView) :
    (bounds.canonicalActions runtime leaks who past view).Nonempty :=
  ⟨⟨none⟩, bounds.silence_canonical runtime leaks who past view⟩

def canonicalMenu : (runtime.reactiveApplication leaks).ResponseMenu where
  actions := bounds.canonicalActions runtime leaks
  nonempty := bounds.canonicalActions_nonempty runtime leaks

theorem canonicalActions_effective (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView) :
    bounds.canonicalActions runtime leaks who past view ⊆
      (bounds.menu runtime leaks).actions who past view := by
  classical
  exact Finset.inter_subset_right

theorem canonicalActions_firstSubmission (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (response : (runtime.reactiveApplication leaks).Action)
    (member : response ∈ bounds.canonicalActions runtime leaks who past view) :
    runtime.firstSubmission leaks past response = true := by
  classical
  rcases Finset.mem_union.mp (Finset.mem_inter.mp member).1 with decision | silent
  · exact (Finset.mem_filter.mp decision).2
  · cases Finset.mem_singleton.mp silent
    rfl

/-- Retained silence is the only alternative to a first timely canonical
decision at the player's own ready event. -/
theorem canonicalActions_cases (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (response : (runtime.reactiveApplication leaks).Action)
    (member : response ∈ bounds.canonicalActions runtime leaks who past view) :
    response = ⟨none⟩ ∨ ∃ event choice,
      view.application.publicView.ownTurn? who = some event ∧
      graph.actor? event = some who ∧ view.application.publicView.EventReady event ∧
      view.application.publicView.WithinDeadline runtime event ∧
      choice ∈ bounds.canonicalChoices event ∧
      runtime.firstSubmission leaks past response = true ∧
      response = runtime.canonicalServiceDecision leaks who past view event choice := by
  classical
  rcases Finset.mem_union.mp (Finset.mem_inter.mp member).1 with decision | silent
  · obtain ⟨chosen, first⟩ := Finset.mem_filter.mp decision
    cases selected : view.application.publicView.ownTurn? who with
    | none => simp only [canonicalDecisionActions, selected, Finset.notMem_empty] at chosen
    | some event =>
        simp only [canonicalDecisionActions, selected] at chosen
        split at chosen
        · rename_i active
          obtain ⟨choice, available, same⟩ := Finset.mem_image.mp chosen
          exact Or.inr ⟨event, choice, rfl, active.1, active.2.1, active.2.2,
            available, first, same.symm⟩
        · simp only [Finset.notMem_empty] at chosen
  · exact Or.inl (Finset.mem_singleton.mp silent)

/-- Every actual submission is a first call of the owner's ready, timely turn. -/
theorem canonical_submitted_event (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (response : (runtime.reactiveApplication leaks).Action)
    (member : response ∈ bounds.canonicalActions runtime leaks who past view)
    (event : graph.EventId) (submitted : runtime.submittedEvent? leaks response = some event) :
    view.application.publicView.ownTurn? who = some event ∧
      graph.actor? event = some who ∧ view.application.publicView.EventReady event ∧
      view.application.publicView.WithinDeadline runtime event ∧
      runtime.eventRecorded leaks past event = false := by
  rcases bounds.canonicalActions_cases runtime leaks who past view response member with rfl |
    ⟨other, choice, turn, owned, ready, timely, _, first, same⟩
  · cases submitted
  · have shape := runtime.canonicalServiceDecision_submittedEvent leaks who past view other choice
    rw [← same] at shape
    rcases shape with absent | named
    · rw [submitted] at absent
      cases absent
    · have equal : other = event := Option.some.inj (named.symm.trans submitted)
      subst other
      have unsent : runtime.eventRecorded leaks past event = false := by
        simpa only [firstSubmission, submitted, Bool.not_eq_true_eq_eq_false] using first
      exact ⟨turn, owned, ready, timely, unsent⟩

/-- Every emitted retained response is a canonical decision at an unrecorded
owned event. This shape is independent of the scheduler's delivery bound. -/
theorem canonicalActions_submission (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (response : (runtime.reactiveApplication leaks).Action)
    (member : response ∈ bounds.canonicalActions runtime leaks who past view)
    (material : (runtime.reactiveApplication leaks).Submission)
    (emitted : response.transmission = some material) :
    ∃ event choice,
      view.application.publicView.ownTurn? who = some event ∧
      graph.actor? event = some who ∧ view.application.publicView.EventReady event ∧
      view.application.publicView.WithinDeadline runtime event ∧
      runtime.eventRecorded leaks past event = false ∧
      choice ∈ bounds.canonicalChoices event ∧
      response = runtime.canonicalServiceDecision leaks who past view event choice := by
  rcases bounds.canonicalActions_cases runtime leaks who past view response member with rfl |
    ⟨event, choice, turn, owned, ready, timely, represented, first, same⟩
  · cases emitted
  · rcases runtime.canonicalServiceDecision_cases leaks who past view event choice with silent |
      named
    · rw [← same] at silent
      rw [silent] at emitted
      cases emitted
    · rw [← same] at named
      have unsent : runtime.eventRecorded leaks past event = false := by
        simpa only [firstSubmission, named, Bool.not_eq_true_eq_eq_false] using first
      exact ⟨event, choice, turn, owned, ready, timely, unsent, represented, same⟩

/-- Recording an event excludes every later fresh response naming it. -/
theorem canonical_no_second_submission (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (event : graph.EventId) (recorded : runtime.eventRecorded leaks past event = true)
    (response : (runtime.reactiveApplication leaks).Action)
    (member : response ∈ bounds.canonicalActions runtime leaks who past view) :
    runtime.submittedEvent? leaks response ≠ some event := by
  intro submitted
  have first := bounds.canonicalActions_firstSubmission runtime leaks who past view response member
  rw [runtime.firstSubmission_false_of_recorded leaks past event recorded response submitted]
    at first
  cases first

/-- Local source-choice coverage needs boundedness and acceptance timeliness,
but no roster or protected-delivery premise. -/
theorem canonical_decision_retained (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (event : graph.EventId) (choice : graph.Action event)
    (turn : view.application.publicView.ownTurn? who = some event)
    (owned : graph.actor? event = some who)
    (ready : view.application.publicView.EventReady event)
    (timely : view.application.publicView.WithinDeadline runtime event)
    (unsent : runtime.eventRecorded leaks past event = false)
    (represented : choice ∈ bounds.canonicalChoices event)
    (available : runtime.canonicalServiceDecision leaks who past view event choice ∈
      (bounds.menu runtime leaks).actions who past view) :
    runtime.canonicalServiceDecision leaks who past view event choice ∈
      bounds.canonicalActions runtime leaks who past view := by
  classical
  apply Finset.mem_inter.mpr
  refine ⟨Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨?_, ?_⟩), available⟩
  · simp only [canonicalDecisionActions, turn, owned, ready, timely, and_self, ↓reduceIte]
    exact Finset.mem_image.mpr ⟨choice, represented, rfl⟩
  · exact runtime.canonicalServiceDecision_firstSubmission leaks who past view event choice unsent

/-- The stronger protected-delivery gate implies retained-menu timeliness.
Source admission and bounded packet evidence remain separate premises. -/
theorem protected_canonical_decision_retained (bound : graph.EventId → Nat) (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (event : graph.EventId) (choice : graph.Action event)
    (turn : view.application.publicView.ownTurn? who = some event)
    (owned : graph.actor? event = some who)
    (ready : view.application.publicView.EventReady event)
    (fits : view.application.publicView.InclusionFitsDeadline runtime bound event)
    (unsent : runtime.eventRecorded leaks past event = false)
    (represented : choice ∈ bounds.canonicalChoices event)
    (available : runtime.canonicalServiceDecision leaks who past view event choice ∈
      (bounds.menu runtime leaks).actions who past view) :
    runtime.canonicalServiceDecision leaks who past view event choice ∈
      bounds.canonicalActions runtime leaks who past view :=
  bounds.canonical_decision_retained runtime leaks who past view event choice turn owned ready
    fits.withinDeadline unsent represented available

/-- Every covered typed binding value is retained at the selected canonical
slot, including after earlier bindings completed by expiry. -/
theorem canonical_binding_value_retained (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding who payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind who payload)
    (node : nodeView graph event = .bind who payload outputEq codeEq)
    (turn : view.application.publicView.ownTurn? who = some event)
    (owned : graph.actor? event = some who)
    (ready : view.application.publicView.EventReady event)
    (timely : view.application.publicView.WithinDeadline runtime event)
    (unsent : runtime.eventRecorded leaks past event = false)
    (serial : Nat) (selected : canonicalFreshSlot who view.application = some serial)
    (capacity : serial < bounds.candidateCount)
    (value : L.Val payload) (included : (⟨payload, value⟩ : Raw L) ∈ bounds.values) :
    runtime.canonicalServiceDecision leaks who past view event
        (cast (congrArg EventField.Action outputEq.symm) (PublicationResult.success value)) ∈
      bounds.canonicalActions runtime leaks who past view := by
  classical
  apply bounds.canonical_decision_retained runtime leaks who past view event _ turn owned ready
    timely unsent
  · simp only [canonicalChoices, node]
    exact Finset.mem_image.mpr ⟨value, (bounds.typedValues_mem payload value).mpr
      ⟨⟨payload, value⟩, included, Raw.as?_mk payload value⟩, rfl⟩
  · rw [runtime.canonicalServiceDecision_binding leaks who past view event payload outputEq
      codeEq node serial selected]
    rw [← runtime.reactiveBinding_normal_of_fresh leaks who past view event payload
      (.success value) serial (canonicalFreshSlot_spec who view.application serial selected)]
    exact bounds.binding_normalized_available runtime leaks who past view event payload _ serial
      capacity (fun chosen same => by
        cases PublicationResult.success.inj same
        exact included)

/-- Both resolution choices are retained whenever their actual selected packet
fits the bounds. Failed guards and withholding normalize to silence. -/
theorem canonical_resolution_retained (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (event : graph.EventId) (actor : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding actor payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve actor payload binding checks)
    (node : nodeView graph event = .resolve actor payload binding checks outputEq codeEq)
    (turn : view.application.publicView.ownTurn? who = some event)
    (owned : graph.actor? event = some who)
    (ready : view.application.publicView.EventReady event)
    (timely : view.application.publicView.WithinDeadline runtime event)
    (unsent : runtime.eventRecorded leaks past event = false)
    (choice : Bool)
    (allowed : ∀ packet, reactiveResolutionPacket who event payload binding checks outputEq
      (cast (congrArg EventField.Action outputEq.symm) choice) view.application = some packet →
        bounds.AllowsPacket packet) :
    runtime.canonicalServiceDecision leaks who past view event
        (cast (congrArg EventField.Action outputEq.symm) choice) ∈
      bounds.canonicalActions runtime leaks who past view := by
  classical
  apply bounds.canonical_decision_retained runtime leaks who past view event _ turn owned ready
    timely unsent
  · simp only [canonicalChoices, node]
    exact Finset.mem_image.mpr ⟨choice, Finset.mem_univ _, rfl⟩
  · apply bounds.canonicalServiceDecision_available runtime leaks who past view
    cases sent : reactiveResolutionPacket who event payload binding checks outputEq
        (cast (congrArg EventField.Action outputEq.symm) choice) view.application with
    | none =>
      simp only [canonicalReactiveDecision, node, sent, Option.map_none]
      exact (ReactiveApplication.ResponseMenu.fromSubmissions_mem
        (app := runtime.reactiveApplication leaks)
        (fun _ past view => bounds.submissions
          (ReactiveApplication.ResponseMenu.knownPackets past view)) who past view _).mpr trivial
    | some packet =>
    simp only [canonicalReactiveDecision, node, sent, Option.map_some]
    apply (ReactiveApplication.ResponseMenu.fromSubmissions_mem
      (app := runtime.reactiveApplication leaks)
      (fun _ past view => bounds.submissions
        (ReactiveApplication.ResponseMenu.knownPackets past view)) who past view _).mpr
    have rawAllowed := bounds.disclosureSubmission_allowed _ [] (allowed packet sent)
    have normalized := (bounds.submissions_mem _ _).mp
      (bounds.normalize_submission_mem who view.application _ _
        ((bounds.submissions_mem _ _).mpr rawAllowed))
    exact (bounds.submissions_mem _ _).mpr
      ⟨normalized.1, bounds.allowsEvidence_mono (List.nil_subset _) _ normalized.2⟩

end MessageBounds

end Vegas.EventGraphRuntime
