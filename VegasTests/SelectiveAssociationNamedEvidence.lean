/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationSourceCalendar
import Interaction.ReactivePacketEvidence

/-! # Sound named certificates in the source service

Certificates are facts of the actual source context. None is available before
the first binding, and every issued or forwarded certificate remains true at
all compatible histories. This does not identify an uncertified claim with an
opening certificate or assert any sequential-rationality conclusion.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation.NamedSource

open Vegas Vegas.SourceProgram Interaction GameTheory.Math.Probability

theorem initial_no_evidence (fact : CommitmentEvidence Player simpleExpr) :
    ¬ initialCore.evidenceHolds sourceProgram fact := by
  change ¬ fact.Holds (Env.empty _)
  rintro ⟨reference, _⟩
  exact nomatch reference

theorem no_initial_owned (who : Player) (fact : NamedFact) : ¬ initial.owns who fact := by
  intro owned
  exact initial_no_evidence fact.toSource (owns_sound initial who fact owned)

def packetEvidence (Claim : Type) : (application Claim).PacketEvidence where
  Fact := NamedFact
  valid state fact := state.core.evidenceHolds sourceProgram fact.toSource
  decode message := message.evidence.toList
  persists fact := {
    submit state who material valid := submit_evidence state who material fact.toSource valid
    handle state message next valid accepted := by
      change some state = some next at accepted
      cases Option.some.inj accepted
      exact valid
    environment state cmd next valid reached := by
      change next ∈ (FinDist.pure (command state cmd)).support at reached
      cases FinDist.mem_support_pure.mp reached
      exact command_evidence state cmd fact.toSource valid }
  issued state who known material received fact certified := by
    classical
    change fact ∈ (certificates state who known material).toList at certified
    simp only [Finset.mem_toList, certificates, Finset.mem_union] at certified
    rcases certified with requested | opened
    · have available := (Finset.mem_filter.mp requested).2
      rcases available with owned | ⟨message, member, carried⟩
      · exact owns_sound state who fact owned
      · exact received message member fact (Finset.mem_toList.mpr carried)
    · split at opened
      · exact owns_sound state who fact (Finset.mem_filter.mp opened).2.1
      · exact False.elim (Finset.notMem_empty fact opened)

theorem certificates_initial {Claim : Type} (who : Player) (submission : Submission Claim) :
    certificates initial who [] submission = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro fact present
  have certified := (packetEvidence Claim).issued initial who [] submission
    (by simp) fact (Finset.mem_toList.mpr present)
  exact initial_no_evidence fact.toSource certified

private theorem reference_member {context : SourceCtx Player simpleExpr}
    {name : VarId} {cell : CellTy Player simpleExpr} (reference : HasVar context name cell) :
    (name, cell) ∈ context := by
  induction reference with
  | here => exact List.mem_cons_self
  | there _ ih => exact List.mem_cons_of_mem _ ih

/-- The six named facts cover every possible genuine commitment fact of the
actual source context. The message alphabet excludes no additional binding. -/
theorem namedFacts_complete (core : SourceCore) (fact : CommitmentEvidence Player simpleExpr)
    (known : core.evidenceHolds sourceProgram fact) :
    ∃ named : NamedFact, named.toSource = fact := by
  rcases fact with ⟨owner, name, payload, value⟩
  rcases core with config | config | config | config | config | config | config
  all_goals
    simp only [sourceProgram, ProtocolState.evidenceHolds, Sum.elim_inl, Sum.elim_inr] at known
    obtain ⟨reference, _⟩ := known
    have member := reference_member reference
    simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, CellTy.commitment.injEq,
      reduceCtorEq, and_false, false_or, or_false] at member
  all_goals
    rcases member with (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
  all_goals
    try casesm* _ ∧ _
    subst_vars
    first
    | exact ⟨(0, value), rfl⟩
    | exact ⟨(1, value), rfl⟩
    | exact ⟨(2, value), rfl⟩

theorem observed_fact_known (Claim : Type) [Fintype Claim]
    (who : Player) (past : List (application Claim).PlayerEntry)
    (view : (application Claim).PlayerView) (fact : NamedFact)
    (observed : fact ∈ (packetEvidence Claim).observe view) :
    (model Claim).Knows who (some (past, view)) (fun history =>
      ReactiveApplication.stateInvariant
        (app := application Claim)
        (fun state => state.core.evidenceHolds sourceProgram fact.toSource) history.state) :=
  (packetEvidence Claim).knows_observed_menu (menu Claim) (FinDist.pure initial) horizon
    (scheduler Claim) who past view fact observed

theorem owns_alice (a : PublicationResult Bool) (visit : Option Event) (clock : Nat)
    (who : Player) (fact : NamedFact) :
    (State.mk (CorePath.alice a) visit clock).owns who fact ↔
      who = SelectiveAssociation.alice ∧ fact.1 = 0 ∧ a = .success fact.2 := by
  change fact.toSource.Possessed who (sourceObserve who (CorePath.aliceBound a).state) ↔ _
  constructor
  · rintro ⟨owner, reference, observed⟩
    have index : fact.1 = 0 := by
      apply Fin.ext
      have named := reference.mem_map_fst
      simpa [NamedFact.toSource, sourceSetup] using named
    rcases fact with ⟨binding, bit⟩
    dsimp only at index
    subst binding
    change SelectiveAssociation.alice = who at owner
    subst who
    refine ⟨rfl, rfl, ?_⟩
    cases reference with
    | here => exact Option.some.inj observed
    | there reference => cases reference
  · rintro ⟨rfl, index, value⟩
    rcases fact with ⟨binding, bit⟩
    dsimp only at index value
    subst binding
    refine ⟨rfl, .here, ?_⟩
    change some a = some (.success bit)
    rw [value]

theorem owns_carol (a c : PublicationResult Bool) (visit : Option Event) (clock : Nat)
    (who : Player) (fact : NamedFact) :
    (State.mk (CorePath.carol a c) visit clock).owns who fact ↔
      (who = SelectiveAssociation.alice ∧ fact.1 = 0 ∧ a = .success fact.2) ∨
      (who = SelectiveAssociation.carol ∧ fact.1 = 1 ∧ c = .success fact.2) := by
  change fact.toSource.Possessed who (sourceObserve who (CorePath.carolBound a c).state) ↔ _
  constructor
  · rintro ⟨owner, reference, observed⟩
    have index : fact.1 = 1 ∨ fact.1 = 0 := by
      have named := reference.mem_map_fst
      have values : fact.1.val = 1 ∨ fact.1.val = 0 := by
        simpa [NamedFact.toSource, sourceSetup] using named
      exact values.imp Fin.ext Fin.ext
    rcases index with index | index
    · rcases fact with ⟨binding, bit⟩
      dsimp only at index
      subst binding
      change SelectiveAssociation.carol = who at owner
      subst who
      refine Or.inr ⟨rfl, rfl, ?_⟩
      cases reference with
      | here => exact Option.some.inj observed
      | there reference => cases reference with
        | there reference => cases reference
    · rcases fact with ⟨binding, bit⟩
      dsimp only at index
      subst binding
      change SelectiveAssociation.alice = who at owner
      subst who
      refine Or.inl ⟨rfl, rfl, ?_⟩
      cases reference with
      | there reference => cases reference with
        | here => exact Option.some.inj observed
        | there reference => cases reference
  · rintro (⟨rfl, index, value⟩ | ⟨rfl, index, value⟩)
    · rcases fact with ⟨binding, bit⟩
      dsimp only at index value
      subst binding
      refine ⟨rfl, .there .here, ?_⟩
      change some a = some (.success bit)
      rw [value]
    · rcases fact with ⟨binding, bit⟩
      dsimp only at index value
      subst binding
      refine ⟨rfl, .here, ?_⟩
      change some c = some (.success bit)
      rw [value]

theorem bob_owns_none_before_guess (a c : PublicationResult Bool)
    (visit : Option Event) (clock : Nat) (fact : NamedFact) :
    ¬ (State.mk (CorePath.carol a c) visit clock).owns bob fact := by
  rw [owns_carol]
  simp [bob, alice, carol]

theorem carol_owns_independent (first second c : PublicationResult Bool)
    (visit : Option Event) (clock : Nat) (fact : NamedFact) :
    (State.mk (CorePath.carol first c) visit clock).owns carol fact ↔
      (State.mk (CorePath.carol second c) visit clock).owns carol fact := by
  simp only [owns_carol, show carol ≠ alice by decide, false_and, false_or]

theorem source_alice_hidden_from_carol (first second : PublicationResult Bool) :
    ProtocolState.observe SelectiveAssociation.carol sourceProgram (CorePath.alice first) =
      ProtocolState.observe SelectiveAssociation.carol sourceProgram (CorePath.alice second) := by
  simp only [ProtocolState.observe, sourceProgram, CorePath.alice, Sum.elim_inl, Sum.elim_inr,
    Sum.inr.injEq, Sum.inl.injEq, Config.view, Prod.mk.injEq]
  constructor
  · apply sourceObserve_congr <;> intro name payload reference <;> cases reference with
    | there reference => cases reference
  · simp [CorePath.aliceBound, commitSuccessor, alice, carol]

theorem source_alice_hidden_from_bob (first second : PublicationResult Bool) :
    ProtocolState.observe SelectiveAssociation.bob sourceProgram (CorePath.alice first) =
      ProtocolState.observe SelectiveAssociation.bob sourceProgram (CorePath.alice second) := by
  simp only [ProtocolState.observe, sourceProgram, CorePath.alice, Sum.elim_inl, Sum.elim_inr,
    Sum.inr.injEq, Sum.inl.injEq, Config.view, Prod.mk.injEq]
  constructor
  · apply sourceObserve_congr <;> intro name payload reference <;> cases reference with
    | there reference => cases reference
  · simp [CorePath.aliceBound, commitSuccessor, alice, bob]

theorem source_carol_hidden_from_bob (first second guess : PublicationResult Bool) :
    ProtocolState.observe SelectiveAssociation.bob sourceProgram (CorePath.carol first guess) =
      ProtocolState.observe SelectiveAssociation.bob sourceProgram
        (CorePath.carol second guess) := by
  simp only [ProtocolState.observe, sourceProgram, CorePath.carol, Sum.elim_inl, Sum.elim_inr,
    Sum.inr.injEq, Sum.inl.injEq, Config.view, Prod.mk.injEq]
  constructor
  · apply sourceObserve_congr <;> intro name payload reference <;> cases reference with
    | there reference => cases reference with
      | there reference => cases reference
  · simp [CorePath.carolBound, CorePath.aliceBound, commitSuccessor, alice, bob, carol]

end VegasTests.SelectiveAssociation.NamedSource
