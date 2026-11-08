/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReactiveValueSwap
import Vegas.Pending.ReactiveOnePacketMenu
import Vegas.Pending.ValueSwapPairs

/-! # Hidden swaps keep one-packet responses available

A hidden swap changes a player's own candidates and observation and the value a
commitment prepares, but no packet, no known envelope and no count verdict. So a
response of the one-packet menu whose evidence request the swap fixes, swapped,
is a response of the one-packet menu at the swapped recall and view, provided
the bounded values are closed under the swap
(`Vegas.EventGraphRuntime.MessageBounds.swap_mem_onePacketActions`).
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction Vegas.EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}
  {timeouts : EventTimeouts graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}

omit [DecidableEq Player] [IExpr.ResultTypes L] in
theorem swapCandidate_eq_openable_iff {swap : Raw L → Raw L} (involutive : Function.Involutive swap)
    (candidate : CommitmentCandidate (Raw L)) (raw : Raw L) :
    swapCandidate swap candidate = .openable raw ↔ candidate = .openable (swap raw) := by
  cases candidate with
  | fresh | unopenable => simp
  | openable value =>
      simp only [swapCandidate_openable, CommitmentCandidate.openable.injEq]
      constructor
      · rintro rfl
        exact (involutive value).symm
      · rintro rfl
        exact involutive raw

namespace HiddenSwap

variable (swap : HiddenSwap graph)

/-- A player's own candidates, swapped at that player's handles. -/
def ownCandidates (who : Player) (candidates : CandidateSlot graph → CommitmentCandidate (Raw L)) :
    CandidateSlot graph → CommitmentCandidate (Raw L) :=
  fun slot => swapCandidate (swap.raw (who, slot)) (candidates slot)

theorem knownPackets_entry (past : List ((reactiveApplication timeouts) leaks).PlayerEntry)
    (observed : ((reactiveApplication timeouts) leaks).PlayerView) :
    ReactiveApplication.ResponseMenu.knownPackets (past.map swap.entry) (swap.view observed) =
      ReactiveApplication.ResponseMenu.knownPackets past observed := by
  simp only [ReactiveApplication.ResponseMenu.knownPackets, ReactiveApplication.outputs,
    List.filterMap_map]
  rfl

theorem submissionCount_entry (past : List ((reactiveApplication timeouts) leaks).PlayerEntry) :
    ((reactiveApplication timeouts) leaks).submissionCount (past.map swap.entry) =
      ((reactiveApplication timeouts) leaks).submissionCount past := by
  simp only [ReactiveApplication.submissionCount, List.countP_map]
  congr 1
  funext recalled
  rcases recalled with ⟨_, ⟨transmission⟩, _⟩
  cases transmission <;> rfl

theorem candidateAfter_swap (submission : Submission graph) (who : Player)
    (candidates : CandidateSlot graph → CommitmentCandidate (Raw L)) (query : CandidateSlot graph) :
    (submission.swap swap).candidateAfter who (swap.ownCandidates who candidates) query =
      swapCandidate (swap.raw (who, query)) (submission.candidateAfter who candidates query) := by
  rcases submission with ⟨packet, opening⟩
  cases packet with
  | commitment event candidate =>
      rcases candidate with ⟨owner, slot⟩
      simp only [Submission.candidateAfter, Submission.swap]
      split
      · rename_i owned
        obtain ⟨rfl, rfl⟩ := owned
        simp only [ownCandidates]
        cases meaning : candidates query with
        | fresh =>
            simp only [swapCandidate_fresh]
            cases query <;> cases opening <;> rfl
        | openable raw => rfl
        | unopenable => rfl
      · rfl
  | opening | malformed => rfl

theorem resolve_swap (request : EvidenceRequest graph) (who : Player)
    (candidates : CandidateSlot graph → CommitmentCandidate (Raw L))
    (known : List (Message Player (WitnessedPacket graph))) (fixed : request.FixedBy swap) :
    request.resolve who (swap.ownCandidates who candidates) known =
      request.resolve who candidates known := by
  cases request with
  | none | forward => rfl
  | owned fact =>
      change swap.raw fact.handle fact.raw = fact.raw at fixed
      have condition : (fact.handle.1 = who ∧
          swap.ownCandidates who candidates fact.handle.2 = .openable fact.raw) ↔
          (fact.handle.1 = who ∧ candidates fact.handle.2 = .openable fact.raw) := by
        constructor
        · rintro ⟨owner, opened⟩
          refine ⟨owner, ?_⟩
          have handleEq : (who, fact.handle.2) = fact.handle := by rw [← owner]
          simp only [ownCandidates, handleEq,
            swapCandidate_eq_openable_iff (swap.raw_involutive _), fixed] at opened
          exact opened
        · rintro ⟨owner, opened⟩
          refine ⟨owner, ?_⟩
          have handleEq : (who, fact.handle.2) = fact.handle := by rw [← owner]
          simp only [ownCandidates, handleEq,
            swapCandidate_eq_openable_iff (swap.raw_involutive _), fixed]
          exact opened
      simp only [EvidenceRequest.resolve, condition]

theorem normalizeReactive_swap (who : Player) (observed : PlayerView graph)
    (submission : Submission graph) :
    (submission.swap swap).normalizeReactive who (PlayerView.swap swap observed) =
      (submission.normalizeReactive who observed).swap swap := by
  classical
  rcases submission with ⟨packet, opening⟩
  have effective : openingEffective who (PlayerView.swap swap observed) packet ↔
      openingEffective who observed packet := by
    cases packet with
    | commitment event candidate =>
        rcases candidate with ⟨owner, slot⟩
        cases slot with
        | initial => exact Iff.rfl
        | prepared serial =>
            simp only [openingEffective, PlayerView.swap, swapCandidate_eq_fresh_iff]
    | opening | malformed => exact Iff.rfl
  simp only [Submission.normalizeReactive, Submission.swap, effective]
  split <;> cases packet <;> rfl

theorem witnessedNormalize_swap (who : Player) (observed : PlayerView graph)
    (whoEq : observed.who = who) (known : List (Message Player (WitnessedPacket graph)))
    (submission : WitnessedSubmission graph) (fixed : submission.evidence.FixedBy swap) :
    (submission.swap swap).normalizeReactive who (PlayerView.swap swap observed) known =
      (submission.normalizeReactive who observed known).swap swap := by
  have candidates : (submission.swap swap).call.candidateAfter who
      (PlayerView.swap swap observed).candidates =
      swap.ownCandidates who (submission.call.candidateAfter who observed.candidates) := by
    funext query
    have := swap.candidateAfter_swap submission.call who observed.candidates query
    rw [← whoEq] at this ⊢
    exact this
  change WitnessedSubmission.mk
      ((submission.swap swap).call.normalizeReactive who (PlayerView.swap swap observed))
      (EvidenceRequest.normalize who ((submission.swap swap).call.candidateAfter who
        (PlayerView.swap swap observed).candidates) known (submission.swap swap).evidence) =
    WitnessedSubmission.mk ((submission.call.normalizeReactive who observed).swap swap)
      (EvidenceRequest.normalize who (submission.call.candidateAfter who observed.candidates)
        known submission.evidence)
  rw [WitnessedSubmission.swap_call] at candidates
  rw [WitnessedSubmission.swap_call, normalizeReactive_swap, candidates,
    WitnessedSubmission.swap_evidence]
  unfold EvidenceRequest.normalize
  rw [swap.resolve_swap _ who _ _ fixed]

end HiddenSwap

namespace MessageBounds

variable [Fintype Player] (bounds : MessageBounds graph) (swap : HiddenSwap graph)

/-- **Swapped one-packet responses stay available.** -/
theorem swap_mem_onePacketActions (who : Player)
    (past : List ((reactiveApplication timeouts) leaks).PlayerEntry)
    (observed : ((reactiveApplication timeouts) leaks).PlayerView)
    (whoEq : observed.application.who = who)
    (response : ((reactiveApplication timeouts) leaks).Action)
    (member : response ∈ bounds.onePacketActions timeouts leaks who past observed)
    (fixed : swap.RequestFixed response)
    (bounded : ∀ handle raw, raw ∈ bounds.values → swap.raw handle raw ∈ bounds.values) :
    swap.action response ∈ bounds.onePacketActions timeouts leaks who (past.map swap.entry)
      (swap.view observed) := by
  rw [mem_onePacketActions] at member ⊢
  obtain ⟨menuMember, onePacket⟩ := member
  rw [menu_mem] at menuMember ⊢
  obtain ⟨allowed, normal⟩ := menuMember
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => exact ⟨⟨trivial, rfl⟩, Or.inl rfl⟩
  | some submission =>
      have fixedHere := fixed submission rfl
      have normalHere : submission.normalizeReactive who observed.application
          (ReactiveApplication.ResponseMenu.knownPackets past observed) = submission :=
        Option.some.inj (congrArg ReactiveApplication.Action.transmission normal)
      have candidates : (submission.swap swap).call.candidateAfter who
          (PlayerView.swap swap observed.application).candidates =
          swap.ownCandidates who (submission.call.candidateAfter who
            observed.application.candidates) := by
        funext query
        have := swap.candidateAfter_swap submission.call who observed.application.candidates query
        rw [WitnessedSubmission.swap_call]
        change (submission.call.swap swap).candidateAfter who
          (swap.ownCandidates observed.application.who observed.application.candidates) query = _
        rw [whoEq]
        exact this
      obtain ⟨⟨packetAllowed, openingAllowed⟩, evidenceAllowed⟩ := allowed
      refine ⟨⟨⟨⟨packetAllowed, ?_⟩, ?_⟩, ?_⟩, ?_⟩
      · change bounds.AllowsOpening (submission.call.swap swap).opening
        rcases submissionCall : submission.call with ⟨packet, opening⟩
        rw [submissionCall] at openingAllowed
        cases opening with
        | none => cases packet <;> trivial
        | some raw =>
            cases packet with
            | commitment event candidate => exact bounded candidate raw openingAllowed
            | opening | malformed => exact openingAllowed
      · change bounds.AllowsEvidence (ReactiveApplication.ResponseMenu.knownPackets
          (past.map swap.entry) (swap.view observed)) submission.evidence
        rw [swap.knownPackets_entry]
        exact evidenceAllowed
      · change (⟨some ((submission.swap swap).normalizeReactive who
            (PlayerView.swap swap observed.application)
            (ReactiveApplication.ResponseMenu.knownPackets (past.map swap.entry)
              (swap.view observed)))⟩ : ((reactiveApplication timeouts) leaks).Action) =
          ⟨some (submission.swap swap)⟩
        rw [swap.knownPackets_entry, swap.witnessedNormalize_swap who _ whoEq _ submission
          fixedHere, normalHere]
      · right
        rcases onePacket with silent | ⟨material, sent, permitted⟩
        · cases silent
        · cases sent
          refine ⟨submission.swap swap, rfl, ?_⟩
          have outputsEq : ((reactiveApplication timeouts) leaks).outputs (past.map swap.entry) =
              ((reactiveApplication timeouts) leaks).outputs past := by
            simp only [ReactiveApplication.outputs, List.filterMap_map]
            rfl
          have envelope : (localEnvelope timeouts) leaks who (past.map swap.entry)
              (swap.view observed) (submission.swap swap) =
              (localEnvelope timeouts) leaks who past observed submission := by
            unfold localEnvelope
            rw [swap.submissionCount_entry, swap.knownPackets_entry]
            change Message.mk _ (WitnessedPacket.mk submission.call.packet
              (submission.evidence.resolve who ((submission.swap swap).call.candidateAfter who
                (PlayerView.swap swap observed.application).candidates) _) _) = _
            rw [candidates, swap.resolve_swap _ who _ _ fixedHere]
            rfl
          rw [outputsEq, envelope]
          exact permitted

end MessageBounds

omit [DecidableEq Player] in
/-- The swap of inputs: of each input value. -/
def HiddenSwap.inputs (swap : HiddenSwap graph) (inputs : graph.Inputs) : graph.Inputs :=
  fun input => swap.values.value (.inl input) (inputs input)

/-- **Compatible initial handles.** The swap acts on the candidate every initial
handle has for an input value as on that value. -/
def HiddenSwap.InitialHandlesCompatible (swap : HiddenSwap graph) : Prop :=
  ∀ (input : graph.InputId) (owner : Player) (value : (graph.inputLayout input).Value),
    swapCandidate (swap.raw (owner, .initial input))
        (State.candidateOfValue owner (graph.inputLayout input) value) =
      State.candidateOfValue owner (graph.inputLayout input)
        (swap.values.value (.inl input) value)

omit [DecidableEq Player] in
private theorem candidates_ext
    {first second : CommitmentCandidates Player (CandidateSlot graph) (Raw L)}
    (same : ∀ handle, first.lookup handle = second.lookup handle) : first = second := by
  rcases first with ⟨first⟩
  rcases second with ⟨second⟩
  congr 1
  funext owner slot
  exact same (owner, slot)

/-- **The swap of an initial state** is the initial state of the swapped inputs
when the initial handles are compatible. -/
theorem State.swap_initial (swap : HiddenSwap graph)
    (compatible : swap.InitialHandlesCompatible) (inputs : graph.Inputs) :
    (State.initial inputs).swap swap = State.initial (swap.inputs inputs) := by
  have candidates : swap.candidates (State.initial inputs).candidates =
      (State.initial (swap.inputs inputs)).candidates := by
    apply candidates_ext
    rintro ⟨owner, slot⟩
    rw [HiddenSwap.lookup_candidates, State.initial_candidate, State.initial_candidate]
    cases slot with
    | initial input => exact compatible input owner (inputs input)
    | prepared serial => rfl
  change State.mk _ _ (swap.candidates (State.initial inputs).candidates) _ _ = _
  rw [candidates]
  rfl

omit [IExpr.ResultTypes L] in
private theorem swapCandidate_candidateOfValue (owner : Player) :
    ∀ (kind : EventField Player L) (pair : Option (kind.Value × kind.Value))
      (rawPair : Option (Raw L × Raw L)),
      (∀ payload (kindEq : kind = .binding owner payload),
        (pair = none ∧ rawPair = none) ∨
          ∃ left right : L.Val payload,
            pair = some (cast (congrArg EventField.Value kindEq.symm) (.success left),
              cast (congrArg EventField.Value kindEq.symm) (.success right)) ∧
            rawPair = some (⟨payload, left⟩, ⟨payload, right⟩)) →
      ∀ value : kind.Value,
        swapCandidate (pairSwap rawPair) (State.candidateOfValue owner kind value) =
          State.candidateOfValue owner kind (pairSwap pair value)
  | .publicData _, _, _, _, _ => rfl
  | .publication _, _, _, _, _ => rfl
  | .privateInput _ _, _, _, _, _ => rfl
  | .binding inputOwner payload, pair, rawPair, paired, value => by
      classical
      by_cases same : inputOwner = owner
      · subst same
        rcases paired payload rfl with ⟨pairNone, rawNone⟩ | ⟨left, right, pairEq, rawEq⟩
        · subst pairNone rawNone
          cases value <;> simp [State.candidateOfValue, pairSwap]
        · subst pairEq rawEq
          change PublicationResult (L.Val payload) at value
          cases value with
          | failure =>
              have fixed : pairSwap (some ((PublicationResult.success left :
                  PublicationResult (L.Val payload)), PublicationResult.success right))
                  PublicationResult.failure = PublicationResult.failure :=
                pairSwap_of_ne _ _ _ (by simp) (by simp)
              simp only [cast_eq]
              rw [fixed]
              simp [State.candidateOfValue]
          | success value =>
              simp only [cast_eq]
              rw [pairSwap_map (fun value : L.Val payload =>
                  (PublicationResult.success value : PublicationResult (L.Val payload)))
                (fun _ _ same => PublicationResult.success.inj same)]
              simp only [State.candidateOfValue, ↓reduceIte, swapCandidate_openable]
              rw [pairSwap_map (fun value : L.Val payload => (⟨payload, value⟩ : Raw L))
                (fun _ _ same => by cases same; rfl)]
      · simp [State.candidateOfValue, same]

/-- **Initial handles carrying the raw pairs of their inputs are compatible**
with the swap of pairs: every initial binding handle carries no pair when its
input has none, and the raw pair of the input's pair of two successes
otherwise. -/
theorem HiddenSwap.initialHandlesCompatible_ofPairs (pairs : graph.SwapPairs)
    (handlePairs : Handle graph → Option (Raw L × Raw L))
    (initialPairs : ∀ (input : graph.InputId) (owner : Player) (payload : L.Ty)
      (layoutEq : graph.inputLayout input = .binding owner payload),
      (pairs.pair (.inl input) = none ∧ handlePairs (owner, .initial input) = none) ∨
        ∃ left right : L.Val payload,
          pairs.pair (.inl input) =
            some (cast (congrArg EventField.Value layoutEq.symm) (.success left),
              cast (congrArg EventField.Value layoutEq.symm) (.success right)) ∧
          handlePairs (owner, .initial input) = some (⟨payload, left⟩, ⟨payload, right⟩)) :
    (HiddenSwap.ofPairs pairs handlePairs).InitialHandlesCompatible := by
  intro input owner value
  exact swapCandidate_candidateOfValue owner (graph.inputLayout input) (pairs.pair (.inl input))
    (handlePairs (owner, .initial input)) (initialPairs input owner) value


end Vegas.EventGraphRuntime
