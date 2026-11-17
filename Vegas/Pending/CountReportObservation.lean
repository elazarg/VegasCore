module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.ReactiveCountVerdict
public import Interaction.ReactiveInputOrder
public import Interaction.ReactiveMessageIdentity

@[expose] public section

/-! # Count reports from observed signed envelopes -/

namespace Vegas.EventGraphRuntime

open Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Keep observed violations for which every lower serial from the same sender
is accounted for. The observer can check the serials using the signed IDs. -/
noncomputable def observedCountReports (seen : List (Message Player (WitnessedPacket graph))) :
    List (Message Player (WitnessedPacket graph)) :=
  seen.filter fun message =>
    (List.range message.id.2).all (fun n =>
      seen.any (fun other => other.id == (message.sender, n))) &&
      !countPermits seen message

/-- Under the network's unique-ID invariant, an authentic archive reports
exactly the visible forbidden packets with a complete sender prefix. -/
theorem mem_observedCountReports (network : MessageNetwork Player (WitnessedPacket graph))
    (unique : network.UniqueIds) (seen : List (Message Player (WitnessedPacket graph)))
    (authentic : seen ⊆ network.inputs) (message : Message Player (WitnessedPacket graph)) :
    message ∈ observedCountReports seen ↔
      message ∈ seen ∧
      (∀ n < message.id.2, (message.sender, n) ∈ seen.map Message.id) ∧
      countPermits network.inputs message = false := by
  have agrees (full : ∀ n < message.id.2, (message.sender, n) ∈ seen.map Message.id) :
      countPermits seen message = countPermits network.inputs message := by
    apply countPermits_congr
    intro other
    constructor
    · rintro ⟨member, owner, lower⟩
      exact ⟨authentic member, owner, lower⟩
    · rintro ⟨member, owner, lower⟩
      obtain ⟨copy, observed, id_eq⟩ := List.mem_map.mp (full _ lower)
      have same : copy.id = other.id := id_eq.trans (Prod.ext owner.symm rfl)
      have eq := (unique.inputs other member).inputs copy (authentic observed) same
      exact ⟨eq ▸ observed, owner, lower⟩
  simp only [observedCountReports, List.mem_filter, Bool.and_eq_true, List.all_eq_true,
    List.mem_range, List.any_eq_true, beq_iff_eq, Bool.not_eq_true', List.mem_map]
  constructor
  · rintro ⟨present, full, bad⟩
    exact ⟨present, full, (agrees (fun n hn => List.mem_map.mpr (full n hn))).symm.trans bad⟩
  · rintro ⟨present, full, bad⟩
    exact ⟨present, full, (agrees (fun n hn => List.mem_map.mpr (full n hn))).trans bad⟩

/-- At a legal prefix, an archive containing this sender's complete stream
supplies a single report exactly when the traffic audit contains a violation
by that sender. Other senders' traffic may be entirely absent. -/
theorem observedCountReports_sender_history (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (initial : PMF (State graph)) (horizon : ℕ)
    (scheduler : ((reactiveApplication timeouts) leaks).Scheduler)
    (control : ((reactiveApplication timeouts) leaks).Control)
    (trace : (((reactiveApplication timeouts) leaks).protocol initial horizon scheduler).Trace
      (some control))
    (sender : Player) (seen : List (Message Player (WitnessedPacket graph)))
    (authentic : seen ⊆ control.execution.network.inputs)
    (complete : ∀ m ∈ control.execution.network.inputs, m.sender = sender → m ∈ seen) :
    ((observedCountReports seen).find? (fun m => m.sender == sender)).isSome ↔
      ∃ m ∈ control.execution.network.inputs, m.sender = sender ∧
        countPermits control.execution.network.inputs m = false := by
  let app := (reactiveApplication timeouts) leaks
  have unique := app.uniqueIds_history scheduler initial horizon control trace
  have ordered := app.inputSerialsInOrder_history scheduler initial horizon trace
  have serials := ordered sender
  simp only [List.find?_isSome, beq_iff_eq]
  constructor
  · rintro ⟨m, reported, owner⟩
    obtain ⟨member, _, bad⟩ := (mem_observedCountReports _ unique seen authentic m).mp reported
    exact ⟨m, authentic member, owner, bad⟩
  · rintro ⟨m, member, owner, bad⟩
    refine ⟨m, (mem_observedCountReports _ unique seen authentic m).mpr
      ⟨complete _ member owner, ?_, bad⟩, owner⟩
    intro n lower
    have issued : m.id.2 ∈ List.range (control.execution.network.nextSerial sender) := by
      rw [← serials]
      exact List.mem_map.mpr ⟨m, List.mem_filter.mpr ⟨member, by simp [owner]⟩, rfl⟩
    have prior := List.mem_range.mpr (lower.trans (List.mem_range.mp issued))
    rw [← serials] at prior
    obtain ⟨other, kept, serial⟩ := List.mem_map.mp prior
    obtain ⟨actual, same⟩ := List.mem_filter.mp kept
    have author : other.sender = sender := by simpa using same
    exact List.mem_map.mpr
      ⟨other, complete _ actual author, Prod.ext (author.trans owner.symm) serial⟩

/-- Two complete serial histories agree on the visible binding packet. The
missing predecessor determines whether the binding is first for its event. -/
theorem binding_countVerdicts_differ (sender : Player) (event : graph.EventId)
    (owned : bindingOwnedBy graph sender event = true) (raw : Raw L) :
    ∃ (message first prior : Message Player (WitnessedPacket graph)),
      message.id = (sender, 1) ∧ first.id = (sender, 0) ∧ prior.id = first.id ∧
      message.payload = ⟨.commitment event (sender, .prepared 0), none, some ⟨event⟩⟩ ∧
      first.payload.call = .malformed raw ∧ prior.payload = message.payload ∧
      countPermits [first, message] message = true ∧
      countPermits [prior, message] message = false := by
  let packet : WitnessedPacket graph :=
    ⟨.commitment event (sender, .prepared 0), none, some ⟨event⟩⟩
  let message : Message Player (WitnessedPacket graph) := ⟨(sender, 1), packet⟩
  let first : Message Player (WitnessedPacket graph) := ⟨(sender, 0), ⟨.malformed raw, none, none⟩⟩
  let prior : Message Player (WitnessedPacket graph) := ⟨(sender, 0), packet⟩
  refine ⟨message, first, prior, rfl, rfl, rfl, rfl, rfl, rfl,
    (countPermits_eq_true_iff ..).mpr ?_, ?_⟩
  · have earlier {other} (h : EarlierOwnPacket [first, message] message other) : other = first := by
      rcases (by simpa using h.1 : other = first ∨ other = message) with eq | rfl
      · exact eq
      · exact (Nat.lt_irrefl _ h.2.2).elim
    refine ⟨WitnessedPacket.tokenValid_commitment .., ⟨owned, rfl, rfl, ⟨0, rfl⟩, ?_⟩, ?_⟩
    · intro other h named
      rw [earlier h]
      intro eq
      cases eq
    · intro other h
      rw [earlier h]
      exact nofun
  · apply Bool.eq_false_iff.mpr
    intro accepted
    have firstFor := ((countPermits_eq_true_iff ..).mp accepted).2.2
    exact firstFor prior ⟨by simp, rfl, Nat.zero_lt_succ 0⟩ rfl

/-- For an opening permitted on the full history and resolving a binding
event, an authentic subarchive gives the same verdict exactly when it
contains an earlier signed commitment for that event and handle. -/
theorem opening_permitted_iff_commitment_observed
    (actual seen : List (Message Player (WitnessedPacket graph))) (authentic : seen ⊆ actual)
    (message : Message Player (WitnessedPacket graph)) (event binding : graph.EventId)
    (handle : Handle graph) (raw : Raw L) (call : message.payload.call = .opening event handle raw)
    (resolves : match nodeView graph event with
      | .resolve _ _ ref .. => ref.field = .inr binding
      | _ => False)
    (lawful : countPermits actual message = true) :
    countPermits seen message = true ↔ ∃ prior, EarlierOwnPacket seen message prior ∧
      prior.payload.call = .commitment binding handle := by
  obtain ⟨token, correct, first⟩ := (countPermits_eq_true_iff ..).mp lawful
  have firstSeen : FirstForEvent (EarlierOwnPacket seen message) message :=
    fun prior h => first prior ⟨authentic h.1, h.2⟩
  rw [countPermits_eq_true_iff]
  unfold CountPermits CountPermitsAmong CountCallCorrect
  unfold CountCallCorrect at correct
  simp only [call] at correct ⊢
  cases view : nodeView graph event with
  | bind | sample => simp [view] at resolves
  | resolve owner ty ref checks outputEq codeEq =>
    simp only [view] at resolves correct
    simp only [resolves, SignedBinding] at correct ⊢
    obtain ⟨certified, ownerEq, typed, _⟩ := correct
    constructor
    · rintro ⟨_, ⟨_, _, _, witness⟩, _⟩
      exact witness
    · exact fun witness => ⟨token, ⟨certified, ownerEq, typed, witness⟩, firstSeen⟩

/-- Before a submission is leaked or included, its passive view is identical
to silence. This holds for every observer even when the count verdict forbids
the signed packet. -/
theorem forbiddenSubmission_sameView (sender observer : Player) (call : Payload graph) :
    let net : MessageNetwork Player (WitnessedPacket graph) := .empty
    let (message, after) := net.submit sender ⟨call, none, none⟩
    message ∈ after.inputs ∧ countPermits after.inputs message = false ∧
      after.observe observer = net.observe observer := by
  dsimp only
  refine ⟨by simp [MessageNetwork.submit, MessageNetwork.empty], ?_, rfl⟩
  apply Bool.eq_false_iff.mpr
  intro yes
  have valid := ((countPermits_eq_true_iff ..).mp yes).1
  simp [MessageNetwork.submit] at valid

end Vegas.EventGraphRuntime
