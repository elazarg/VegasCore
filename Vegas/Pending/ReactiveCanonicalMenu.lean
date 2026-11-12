module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.ReactiveCanonicalDecision
public import Vegas.Pending.ReactiveCompiledMenu
public import Vegas.Pending.ReactivePolicyFacts

@[expose] public section

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
theorem canonicalReactiveDecision_transmission (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (event : graph.EventId) (choice : graph.Action event)
    (view : PlayerView graph) :
    ((canonicalReactiveDecision timeouts) leaks who event choice view).transmission = none ∨
      ∃ material,
        ((canonicalReactiveDecision timeouts) leaks who event choice view).transmission =
            some material ∧ material.call.packet.event? graph = some event := by
  by_cases inactive : who ∈ view.publicView.observation.defaulted
  · exact Or.inl (by simp only [canonicalReactiveDecision, ite_eq_left inactive])
  · simp only [canonicalReactiveDecision, ite_eq_right inactive]
    cases node : nodeView graph event with
    | sample => exact Or.inl rfl
    | bind owner payload outputEq codeEq =>
        simp only
        cases chosen : (cast (congrArg EventField.Action outputEq) choice :
            Option (PublicationResult (L.Val payload))) with
        | none => exact Or.inl rfl
        | some result =>
            cases selected : canonicalFreshSlot who view with
            | none => exact Or.inl rfl
            | some serial => exact Or.inr ⟨_, rfl, rfl⟩
    | resolve owner payload binding checks outputEq codeEq =>
        simp only
        cases sent : reactiveResolutionPacket who event payload binding checks outputEq choice
            view with
        | none => exact Or.inl (by simp only [Option.map_none])
        | some packet =>
            exact Or.inr ⟨_, by simp only [Option.map_some]; rfl,
              reactiveResolutionPacket_event who event payload binding checks outputEq choice view
                packet sent⟩

/-- A canonical decision is silent or names exactly its decision event. -/
theorem canonicalServiceDecision_cases (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (past : List ((reactiveApplication timeouts) leaks).PlayerEntry)
    (view : ((reactiveApplication timeouts) leaks).PlayerView)
    (event : graph.EventId) (choice : graph.Action event) :
    (canonicalServiceDecision timeouts) leaks who past view event choice = ⟨none⟩ ∨
      (submittedEvent? timeouts) leaks
        ((canonicalServiceDecision timeouts) leaks who past view event choice) = some event := by
  rcases (canonicalReactiveDecision_transmission timeouts) leaks who event choice view.application
      with silent | ⟨material, emitted, named⟩
  · have same : (canonicalReactiveDecision timeouts) leaks who event choice view.application =
        ⟨none⟩ := congrArg (fun transmission =>
          (⟨transmission⟩ : ((reactiveApplication timeouts) leaks).Action)) silent
    left
    simpa only [canonicalServiceDecision, same] using
      (show ((reactiveNormalization timeouts) leaks).action who past view ⟨none⟩ = ⟨none⟩ from rfl)
  · have same : (canonicalReactiveDecision timeouts) leaks who event choice view.application =
        ⟨some material⟩ := congrArg (fun transmission =>
          (⟨transmission⟩ : ((reactiveApplication timeouts) leaks).Action)) emitted
    obtain ⟨⟨packet, opening⟩, evidence⟩ := material
    cases packet with
    | commitment other candidate | opening other candidate raw | malformed raw =>
        right
        simp only [canonicalServiceDecision, same]
        rw [(submittedEvent_normalization timeouts)]
        exact named

/-- Semantic normalization preserves the submitted event identity. -/
theorem canonicalServiceDecision_submittedEvent (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (past : List ((reactiveApplication timeouts) leaks).PlayerEntry)
    (view : ((reactiveApplication timeouts) leaks).PlayerView)
    (event : graph.EventId) (choice : graph.Action event) :
    (submittedEvent? timeouts) leaks
        ((canonicalServiceDecision timeouts) leaks who past view event choice) = none ∨
      (submittedEvent? timeouts) leaks
        ((canonicalServiceDecision timeouts) leaks who past view event choice) = some event := by
  rcases (canonicalServiceDecision_cases timeouts) leaks who past view event choice with silent |
    named
  · rw [silent]
    exact Or.inl rfl
  · exact Or.inr named

/-- An unrecorded event's canonical decision is a first submission, including
when that decision is represented by silence. -/
theorem canonicalServiceDecision_firstSubmission (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (past : List ((reactiveApplication timeouts) leaks).PlayerEntry)
    (view : ((reactiveApplication timeouts) leaks).PlayerView)
    (event : graph.EventId) (choice : graph.Action event)
    (unsent : (eventRecorded timeouts) leaks past event = false) :
    (firstSubmission timeouts) leaks past
        ((canonicalServiceDecision timeouts) leaks who past view event choice) = true := by
  rcases (canonicalServiceDecision_submittedEvent timeouts) leaks who past view event choice
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
      (bounds.bindingChoices payload).image fun choice =>
        cast (congrArg EventField.Action outputEq.symm) choice
  | .resolve _ _ _ _ outputEq _ =>
      Finset.univ.image fun disclose : Bool =>
        cast (congrArg EventField.Action outputEq.symm) disclose

variable [Fintype Player] (timeouts : EventTimeouts graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

/-- A bounded raw canonical decision is available after normalization or
representation of withholding by silence. -/
theorem canonicalServiceDecision_available (who : Player)
    (past : List ((reactiveApplication timeouts) leaks).PlayerEntry)
    (view : ((reactiveApplication timeouts) leaks).PlayerView)
    (event : graph.EventId) (choice : graph.Action event)
    (available : (canonicalReactiveDecision timeouts) leaks who event choice view.application ∈
      (bounds.rawMenu timeouts leaks).actions who past view) :
    (canonicalServiceDecision timeouts) leaks who past view event choice ∈
      (bounds.menu timeouts leaks).actions who past view := by
  unfold canonicalServiceDecision
  generalize (canonicalReactiveDecision timeouts) leaks who event choice view.application =
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
    (past : List ((reactiveApplication timeouts) leaks).PlayerEntry)
    (view : ((reactiveApplication timeouts) leaks).PlayerView) :
    Finset ((reactiveApplication timeouts) leaks).Action :=
  match view.application.publicView.ownTurn? who with
  | none => ∅
  | some event =>
      if graph.actor? event = some who ∧ view.application.publicView.EventReady event ∧
          view.application.publicView.WithinDeadline timeouts event then
        (bounds.canonicalChoices event).image
          ((canonicalServiceDecision timeouts) leaks who past view event)
      else ∅

open Classical in
/-- Every opportunity retains deferral. A canonical packet may be submitted
only once, and the response must fit the bounded effective menu. -/
def canonicalActions (who : Player)
    (past : List ((reactiveApplication timeouts) leaks).PlayerEntry)
    (view : ((reactiveApplication timeouts) leaks).PlayerView) :
    Finset ((reactiveApplication timeouts) leaks).Action :=
  ((bounds.canonicalDecisionActions timeouts leaks who past view).filter
    (fun response => (firstSubmission timeouts) leaks past response) ∪ {⟨none⟩}) ∩
      (bounds.menu timeouts leaks).actions who past view

theorem silence_canonical (who : Player)
    (past : List ((reactiveApplication timeouts) leaks).PlayerEntry)
    (view : ((reactiveApplication timeouts) leaks).PlayerView) :
    (⟨none⟩ : ((reactiveApplication timeouts) leaks).Action) ∈
      bounds.canonicalActions timeouts leaks who past view := by
  classical
  exact Finset.mem_inter.mpr
    ⟨Finset.mem_union_right _ (Finset.mem_singleton_self _),
      (bounds.menu_mem timeouts leaks who past view _).mpr ⟨trivial, rfl⟩⟩

theorem silent_canonical (who : Player)
    (past : List ((reactiveApplication timeouts) leaks).PlayerEntry)
    (view : ((reactiveApplication timeouts) leaks).PlayerView)
    (response : ((reactiveApplication timeouts) leaks).Action)
    (chosen : response ∈ (((reactiveApplication timeouts) leaks).silentPolicy past view).support) :
    response ∈ bounds.canonicalActions timeouts leaks who past view := by
  cases ((reactiveApplication timeouts) leaks).silentPolicy_cases past view response chosen
  exact bounds.silence_canonical timeouts leaks who past view

theorem canonicalActions_nonempty (who : Player)
    (past : List ((reactiveApplication timeouts) leaks).PlayerEntry)
    (view : ((reactiveApplication timeouts) leaks).PlayerView) :
    (bounds.canonicalActions timeouts leaks who past view).Nonempty :=
  ⟨⟨none⟩, bounds.silence_canonical timeouts leaks who past view⟩

def canonicalMenu : ((reactiveApplication timeouts) leaks).ResponseMenu where
  actions := bounds.canonicalActions timeouts leaks
  nonempty := bounds.canonicalActions_nonempty timeouts leaks

theorem canonicalActions_effective (who : Player)
    (past : List ((reactiveApplication timeouts) leaks).PlayerEntry)
    (view : ((reactiveApplication timeouts) leaks).PlayerView) :
    bounds.canonicalActions timeouts leaks who past view ⊆
      (bounds.menu timeouts leaks).actions who past view := by
  classical
  exact Finset.inter_subset_right

/-- Retained silence is the only alternative to a first timely canonical
decision at the player's own ready event. -/
theorem canonicalActions_cases (who : Player)
    (past : List ((reactiveApplication timeouts) leaks).PlayerEntry)
    (view : ((reactiveApplication timeouts) leaks).PlayerView)
    (response : ((reactiveApplication timeouts) leaks).Action)
    (member : response ∈ bounds.canonicalActions timeouts leaks who past view) :
    response = ⟨none⟩ ∨ ∃ event choice,
      view.application.publicView.ownTurn? who = some event ∧
      graph.actor? event = some who ∧ view.application.publicView.EventReady event ∧
      view.application.publicView.WithinDeadline timeouts event ∧
      choice ∈ bounds.canonicalChoices event ∧
      (firstSubmission timeouts) leaks past response = true ∧
      response = (canonicalServiceDecision timeouts) leaks who past view event choice := by
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
    (past : List ((reactiveApplication timeouts) leaks).PlayerEntry)
    (view : ((reactiveApplication timeouts) leaks).PlayerView)
    (response : ((reactiveApplication timeouts) leaks).Action)
    (member : response ∈ bounds.canonicalActions timeouts leaks who past view)
    (event : graph.EventId) (submitted : (submittedEvent? timeouts) leaks response = some event) :
    view.application.publicView.ownTurn? who = some event ∧
      graph.actor? event = some who ∧ view.application.publicView.EventReady event ∧
      view.application.publicView.WithinDeadline timeouts event ∧
      (eventRecorded timeouts) leaks past event = false := by
  rcases bounds.canonicalActions_cases timeouts leaks who past view response member with rfl |
    ⟨other, choice, turn, owned, ready, timely, _, first, same⟩
  · cases submitted
  · have shape := (canonicalServiceDecision_submittedEvent timeouts) leaks who past view other
      choice
    rw [← same] at shape
    rcases shape with absent | named
    · rw [submitted] at absent
      cases absent
    · have equal : other = event := Option.some.inj (named.symm.trans submitted)
      subst other
      have unsent : (eventRecorded timeouts) leaks past event = false := by
        simpa only [firstSubmission, submitted, Bool.not_eq_true_eq_eq_false] using first
      exact ⟨turn, owned, ready, timely, unsent⟩

/-- Every emitted retained response is a canonical decision at an unrecorded
owned event. This shape is independent of the scheduler's delivery bound. -/
theorem canonicalActions_submission (who : Player)
    (past : List ((reactiveApplication timeouts) leaks).PlayerEntry)
    (view : ((reactiveApplication timeouts) leaks).PlayerView)
    (response : ((reactiveApplication timeouts) leaks).Action)
    (member : response ∈ bounds.canonicalActions timeouts leaks who past view)
    (material : ((reactiveApplication timeouts) leaks).Submission)
    (emitted : response.transmission = some material) :
    ∃ event choice,
      view.application.publicView.ownTurn? who = some event ∧
      graph.actor? event = some who ∧ view.application.publicView.EventReady event ∧
      view.application.publicView.WithinDeadline timeouts event ∧
      (eventRecorded timeouts) leaks past event = false ∧
      choice ∈ bounds.canonicalChoices event ∧
      response = (canonicalServiceDecision timeouts) leaks who past view event choice := by
  rcases bounds.canonicalActions_cases timeouts leaks who past view response member with rfl |
    ⟨event, choice, turn, owned, ready, timely, represented, first, same⟩
  · cases emitted
  · rcases (canonicalServiceDecision_cases timeouts) leaks who past view event choice with silent |
      named
    · rw [← same] at silent
      rw [silent] at emitted
      cases emitted
    · rw [← same] at named
      have unsent : (eventRecorded timeouts) leaks past event = false := by
        simpa only [firstSubmission, named, Bool.not_eq_true_eq_eq_false] using first
      exact ⟨event, choice, turn, owned, ready, timely, unsent, represented, same⟩

/-- Local source-choice coverage needs boundedness and acceptance timeliness,
but no roster or protected-delivery premise. -/
theorem canonical_decision_retained (who : Player)
    (past : List ((reactiveApplication timeouts) leaks).PlayerEntry)
    (view : ((reactiveApplication timeouts) leaks).PlayerView)
    (event : graph.EventId) (choice : graph.Action event)
    (turn : view.application.publicView.ownTurn? who = some event)
    (owned : graph.actor? event = some who)
    (ready : view.application.publicView.EventReady event)
    (timely : view.application.publicView.WithinDeadline timeouts event)
    (unsent : (eventRecorded timeouts) leaks past event = false)
    (represented : choice ∈ bounds.canonicalChoices event)
    (available : (canonicalServiceDecision timeouts) leaks who past view event choice ∈
      (bounds.menu timeouts leaks).actions who past view) :
    (canonicalServiceDecision timeouts) leaks who past view event choice ∈
      bounds.canonicalActions timeouts leaks who past view := by
  classical
  apply Finset.mem_inter.mpr
  refine ⟨Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨?_, ?_⟩), available⟩
  · simp only [canonicalDecisionActions, turn, owned, ready, timely, and_self, ↓reduceIte]
    exact Finset.mem_image.mpr ⟨choice, represented, rfl⟩
  · exact (canonicalServiceDecision_firstSubmission timeouts) leaks who past view event choice
      unsent

/-- Every covered typed binding value is retained at the selected canonical
slot, including after earlier bindings completed by expiry. -/
theorem canonical_binding_value_retained (who : Player)
    (past : List ((reactiveApplication timeouts) leaks).PlayerEntry)
    (view : ((reactiveApplication timeouts) leaks).PlayerView)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding who payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind who payload)
    (node : nodeView graph event = .bind who payload outputEq codeEq)
    (turn : view.application.publicView.ownTurn? who = some event)
    (owned : graph.actor? event = some who)
    (ready : view.application.publicView.EventReady event)
    (timely : view.application.publicView.WithinDeadline timeouts event)
    (unsent : (eventRecorded timeouts) leaks past event = false)
    (serial : Nat) (selected : canonicalFreshSlot who view.application = some serial)
    (capacity : serial < bounds.candidateCount)
    (value : L.Val payload) (included : (⟨payload, value⟩ : Raw L) ∈ bounds.values) :
    (canonicalServiceDecision timeouts) leaks who past view event
        (cast (congrArg EventField.Action outputEq.symm) (some (PublicationResult.success value))) ∈
      bounds.canonicalActions timeouts leaks who past view := by
  classical
  by_cases inactive : who ∈ view.application.publicView.observation.defaulted
  · rw [(canonicalServiceDecision_defaulted timeouts) leaks who past view event _ inactive]
    exact bounds.silence_canonical timeouts leaks who past view
  apply bounds.canonical_decision_retained timeouts leaks who past view event _ turn owned ready
    timely unsent
  · simp only [canonicalChoices, node]
    refine Finset.mem_image.mpr ⟨some (.success value), ?_, rfl⟩
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨value, (bounds.typedValues_mem payload value).mpr
      ⟨⟨payload, value⟩, included, Raw.as?_mk payload value⟩, rfl⟩
  · rw [(canonicalServiceDecision_binding timeouts) leaks who past view event payload outputEq
      codeEq node inactive serial selected]
    rw [← (reactiveBinding_normal_of_fresh timeouts) leaks who past view event payload
      (.success value) serial (canonicalFreshSlot_spec who view.application serial selected)]
    exact bounds.binding_normalized_available timeouts leaks who past view event payload _ serial
      capacity (fun chosen same => by
        cases PublicationResult.success.inj same
        exact included)

/-- Both resolution choices are retained whenever their actual selected packet
fits the bounds. Withholding and unavailable opening material use silence. -/
theorem canonical_resolution_retained (who : Player)
    (past : List ((reactiveApplication timeouts) leaks).PlayerEntry)
    (view : ((reactiveApplication timeouts) leaks).PlayerView)
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
    (timely : view.application.publicView.WithinDeadline timeouts event)
    (unsent : (eventRecorded timeouts) leaks past event = false)
    (choice : Bool)
    (allowed : ∀ packet, reactiveResolutionPacket who event payload binding checks outputEq
      (cast (congrArg EventField.Action outputEq.symm) choice) view.application = some packet →
        bounds.AllowsPacket packet) :
    (canonicalServiceDecision timeouts) leaks who past view event
        (cast (congrArg EventField.Action outputEq.symm) choice) ∈
      bounds.canonicalActions timeouts leaks who past view := by
  classical
  by_cases inactive : who ∈ view.application.publicView.observation.defaulted
  · rw [(canonicalServiceDecision_defaulted timeouts) leaks who past view event _ inactive]
    exact bounds.silence_canonical timeouts leaks who past view
  apply bounds.canonical_decision_retained timeouts leaks who past view event _ turn owned ready
    timely unsent
  · simp only [canonicalChoices, node]
    exact Finset.mem_image.mpr ⟨choice, Finset.mem_univ _, rfl⟩
  · apply bounds.canonicalServiceDecision_available timeouts leaks who past view
    cases sent : reactiveResolutionPacket who event payload binding checks outputEq
        (cast (congrArg EventField.Action outputEq.symm) choice) view.application with
    | none =>
      simp only [canonicalReactiveDecision, ite_eq_right inactive, node, sent, Option.map_none]
      exact (ReactiveApplication.ResponseMenu.fromSubmissions_mem
        (app := (reactiveApplication timeouts) leaks)
        (fun _ past view => bounds.submissions
          (ReactiveApplication.ResponseMenu.knownPackets past view)) who past view _).mpr trivial
    | some packet =>
    simp only [canonicalReactiveDecision, ite_eq_right inactive, node, sent, Option.map_some]
    apply (ReactiveApplication.ResponseMenu.fromSubmissions_mem
      (app := (reactiveApplication timeouts) leaks)
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
