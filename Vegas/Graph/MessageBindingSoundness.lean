/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Graph.MessageVerification

/-! # Accepted openings agree with immutable graph bindings

This invariant applies to arbitrary native policies. It supplies the reverse
direction of opening provenance: a successful verification cannot substitute
another value for the graph cell fixed when the commitment was accepted.
-/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory.Math.Probability Interaction Graph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [R : IExpr.ResultTypes L]
variable {Δ : VCtx Player L}

/-- Accepted addresses name existing fields, have fixed candidate meanings,
and verify only the value stored in the corresponding sealed cell. -/
def State.BindingSoundness : State Player L Δ → Prop
  | @State.running _ _ _ _ _ context _ ideal _ bindings candidates _ _ _ =>
      (∀ name handle, lookupBinding bindings name = some handle →
        name ∈ context.map Prod.fst) ∧
      ∀ {name owner ty} (source : HasVar context name (.sealed owner ty)) handle,
        lookupBinding bindings name = some handle →
        candidates.lookup handle ≠ .fresh ∧
        ∀ encoded : L.Val ty, candidates.verify handle ⟨ty, encoded⟩ = true →
          ideal.get source = encoded

/-- Decoding a verified raw opening at an accepted address recovers the
immutable graph cell, including its canonical failure encoding. -/
theorem State.bound_opening_eq {Γ : VCtx Player L}
    (graph : Graph Player L Γ Δ) (ideal : VEnv L Γ) (values : PublicValues Γ)
    (bindings : Bindings Player) (candidates : CommitmentCandidates Player Slot (Raw L))
    (pc clock enteredAt : Nat) {name : VarId} {owner : Player} {ty : L.Ty}
    (source : HasVar Γ name (.sealed owner ty)) (handle : Handle Player)
    (raw : Raw L) (encoded : L.Val ty)
    (sound : State.BindingSoundness
      (State.running graph ideal values bindings candidates pc clock enteredAt))
    (found : lookupBinding bindings name = some handle)
    (verified : candidates.verify handle raw = true) (typed : raw.as? ty = some encoded) :
    ideal.get source = encoded := by
  apply (sound.2 source handle found).2 encoded
  obtain ⟨rawTy, rawValue⟩ := raw
  simp only [Raw.as?] at typed
  split at typed
  · rename_i same
    subst rawTy
    simp only [Option.some.injEq] at typed
    cases typed
    exact verified
  · contradiction

theorem State.initial_bindingSoundness {Γ : VCtx Player L}
    (graph : Graph Player L Γ Δ) (input : VEnv L Γ)
    (unique : (Γ.map Prod.fst).Nodup) : (State.initial graph input).BindingSoundness := by
  refine ⟨State.initial_binding_name graph input, ?_⟩
  intro name owner ty source handle found
  obtain ⟨address, verified⟩ := State.initial_binding graph input unique source
  have same := Option.some.inj (found.symm.trans address)
  subst handle
  have meaning := (CommitmentCandidates.verify_eq_true_iff ..).mp verified
  refine ⟨?_, ?_⟩
  · change (State.initial graph input).candidates.lookup (owner, Slot.initial name) ≠ .fresh
    rw [meaning]
    simp
  intro encoded checked
  have other := (CommitmentCandidates.verify_eq_true_iff ..).mp checked
  have rawEq := CommitmentCandidate.openable.inj (meaning.symm.trans other)
  exact eq_of_heq ((Raw.mk.injEq ..).mp rawEq).2

private theorem privateStep_bindingSoundness (runtime : GraphRuntime Player L Δ)
    (state : State Player L Δ) (who : Player) (command : PrivateCommand L)
    (sound : state.BindingSoundness) :
    (runtime.privateStep state who command).BindingSoundness := by
  cases state with
  | running graph ideal values bindings candidates pc clock enteredAt =>
      cases command with
      | rememberDisclosure => exact sound
      | prepare slot raw =>
          refine ⟨sound.1, ?_⟩
          intro name owner ty source handle found
          obtain ⟨fixed, exactValue⟩ := sound.2 source handle found
          have unchanged := candidates.lookup_prepare_eq_of_not_fresh handle who
            (.prepared slot) raw fixed
          refine ⟨?_, ?_⟩
          · rwa [unchanged]
          · intro encoded verified
            apply exactValue encoded
            rw [CommitmentCandidates.verify_eq_true_iff] at verified ⊢
            exact unchanged ▸ verified

private theorem extendPublic_bindingSoundness {Γ : VCtx Player L}
    (graph : Graph Player L Γ Δ) {name : VarId} {ty : L.Ty}
    (next : Graph Player L ((name, .pub ty) :: Γ) Δ) (value : L.Val ty)
    (ideal : VEnv L Γ) (values : PublicValues Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L))
    (pc clock enteredAt nextPc nextClock nextEntered : Nat)
    (sound : State.BindingSoundness
      (State.running graph ideal values bindings candidates pc clock enteredAt)) :
    (State.running next (VEnv.cons value ideal) (PublicValues.consPublic value values)
      bindings candidates nextPc nextClock nextEntered).BindingSoundness := by
  refine ⟨fun field handle found => List.mem_cons_of_mem _ (sound.1 field handle found), ?_⟩
  intro field owner cellTy source handle found
  cases source with
  | there source => exact sound.2 source handle found

private theorem advanceBindFailure_bindingSoundness {Γ : VCtx Player L}
    {name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst)
    (next : Graph Player L ((name, .sealed owner (R.result payload)) :: Γ) Δ)
    (ideal : VEnv L Γ) (values : PublicValues Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L)) (pc clock enteredAt : Nat)
    (sound : (State.running (.bind name owner fresh next) ideal values bindings candidates
      pc clock enteredAt).BindingSoundness) :
    (advanceBindFailure next ideal values bindings candidates pc clock).BindingSoundness := by
  refine ⟨fun field handle found => List.mem_cons_of_mem _ (sound.1 field handle found), ?_⟩
  intro field fieldOwner ty source handle found
  cases source with
  | here => exact (fresh (sound.1 name handle found)).elim
  | there source => exact sound.2 source handle found

private theorem advanceBind_bindingSoundness {Γ : VCtx Player L}
    {name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst)
    (next : Graph Player L ((name, .sealed owner (R.result payload)) :: Γ) Δ)
    (ideal : VEnv L Γ) (values : PublicValues Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L)) (pc clock enteredAt : Nat)
    (accepted : Handle Player)
    (sound : (State.running (.bind name owner fresh next) ideal values bindings candidates
      pc clock enteredAt).BindingSoundness) :
    (advanceBind next ideal values bindings candidates pc clock accepted).BindingSoundness := by
  constructor
  · intro field handle found
    by_cases same : name = field
    · simp [← same]
    · exact List.mem_cons_of_mem _ (sound.1 field handle
        (by simpa [advanceBind, lookupBinding, same] using found))
  · intro field fieldOwner ty source handle found
    cases source with
    | here =>
        have same : accepted = handle := by
          simpa [lookupBinding] using found
        subst handle
        refine ⟨candidates.lookup_accept_ne_fresh accepted, ?_⟩
        intro encoded verified
        rw [candidates.verify_accept] at verified
        have meaning := (CommitmentCandidates.verify_eq_true_iff ..).mp verified
        simp [meaning, VEnv.get, VEnv.cons, Raw.as?_mk]
    | there source =>
        have different : name ≠ field := fun same => fresh (same ▸ source.mem_map_fst)
        have prior : lookupBinding bindings field = some handle := by
          simpa [lookupBinding, different] using found
        obtain ⟨fixed, exactValue⟩ := sound.2 source handle prior
        refine ⟨?_, ?_⟩
        · rwa [candidates.lookup_accept_eq_of_not_fresh handle accepted fixed]
        · intro encoded verified
          apply exactValue encoded
          exact (candidates.verify_accept accepted handle _).symm ▸ verified

private theorem handle_bindingSoundness (runtime : GraphRuntime Player L Δ)
    (state : State Player L Δ) (message : Message Player (Payload Player L))
    (after : State Player L Δ) (sound : state.BindingSoundness)
    (handled : runtime.handle state message = some after) : after.BindingSoundness := by
  cases state with
  | running graph ideal values bindings candidates pc clock enteredAt =>
      cases graph with
      | ret | sample => cases message.payload <;> simp [handle] at handled
      | bind name owner fresh next =>
          cases packet : message.payload <;> simp only [handle, packet] at handled
          · split_ifs at handled
            cases handled
            exact advanceBind_bindingSoundness fresh next ideal values bindings candidates
              pc clock enteredAt _ sound
          all_goals contradiction
      | resolve output owner binding fresh source checks next =>
          cases packet : message.payload with
          | commitment | malformed => simp [handle, packet] at handled
          | withhold site =>
              simp only [handle, packet] at handled
              split_ifs at handled
              cases handled
              exact extendPublic_bindingSoundness
                (.resolve output owner binding fresh source checks next)
                next _ ideal values bindings candidates
                pc clock enteredAt _ _ _ sound
          | opening site candidate raw =>
              simp only [handle, packet] at handled
              split_ifs at handled
              cases typed : raw.as? _ with
              | none => rw [typed] at handled; contradiction
              | some encoded =>
                  rw [typed] at handled
                  cases handled
                  exact extendPublic_bindingSoundness
                    (.resolve output owner binding fresh source checks next)
                    next _ ideal values bindings candidates
                    pc clock enteredAt _ _ _ sound

private theorem environmentStep_bindingSoundness (runtime : GraphRuntime Player L Δ)
    (state : State Player L Δ) (command : EnvironmentCommand) (after : State Player L Δ)
    (sound : state.BindingSoundness)
    (supported : after ∈ (runtime.environmentStep state command).support) :
    after.BindingSoundness := by
  cases command
  cases state with
  | running graph ideal values bindings candidates pc clock enteredAt =>
      cases graph with
      | ret payoffs =>
          simp only [environmentStep, tick, FinDist.mem_support_pure] at supported
          subst after
          exact sound
      | sample name fresh law next =>
          simp only [environmentStep, tick, FinDist.support_map, Set.mem_image] at supported
          obtain ⟨value, _, rfl⟩ := supported
          exact extendPublic_bindingSoundness (.sample name fresh law next)
            next value ideal values bindings candidates
            pc clock enteredAt _ _ _ sound
      | bind name owner fresh next =>
          simp only [environmentStep, tick] at supported
          split at supported <;> simp only [FinDist.mem_support_pure] at supported <;> subst after
          · exact advanceBindFailure_bindingSoundness fresh next ideal values bindings candidates
              pc (clock + 1) enteredAt sound
          · exact sound
      | resolve output owner binding fresh source checks next =>
          simp only [environmentStep, tick] at supported
          split at supported <;> simp only [FinDist.mem_support_pure] at supported <;> subst after
          · exact extendPublic_bindingSoundness
              (.resolve output owner binding fresh source checks next)
              next _ ideal values bindings candidates
              pc clock enteredAt _ _ _ sound
          · exact sound

/-- Every accepted binding retains sound verification under arbitrary native
commands and policies, including malformed traffic and repeated preparations. -/
theorem run_bindingSoundness (runtime : GraphRuntime Player L Δ)
    (actions : List runtime.application.Action) (state next : runtime.application.State)
    (sound : state.application.BindingSoundness)
    (supported : next ∈ (runtime.application.run actions state).support) :
    next.application.BindingSoundness :=
  runtime.application.run_application_invariant State.BindingSoundness
    (privateStep_bindingSoundness runtime) (handle_bindingSoundness runtime)
    (environmentStep_bindingSoundness runtime) state next actions sound supported

/-- Policy-driven runs inherit the same binding invariant; no sender is
required to follow its compiled policy. -/
theorem runPolicies_bindingSoundness (runtime : GraphRuntime Player L Δ)
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player))
    (execution next : runtime.application.PolicyExecution)
    (sound : execution.native.application.BindingSoundness)
    (supported : next ∈
      (runtime.application.runPolicies players environment schedule execution).support) :
    next.native.application.BindingSoundness := by
  exact runtime.application.runPolicies_application_invariant State.BindingSoundness
    (privateStep_bindingSoundness runtime) (handle_bindingSoundness runtime)
    (environmentStep_bindingSoundness runtime) players environment schedule execution next
    sound supported

theorem runPolicies_initial_bindingSoundness {Γ : VCtx Player L}
    (runtime : GraphRuntime Player L Δ) (graph : Graph Player L Γ Δ) (input : VEnv L Γ)
    (unique : (Γ.map Prod.fst).Nodup)
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player))
    (next : runtime.application.PolicyExecution)
    (supported : next ∈ (runtime.application.runPolicies players environment schedule
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application
          (State.initial graph input)))).support) :
    next.native.application.BindingSoundness :=
  runtime.runPolicies_bindingSoundness players environment schedule _ next
    (State.initial_bindingSoundness graph input unique) supported

end Vegas.GraphRuntime

/-- info: 'Vegas.GraphRuntime.runPolicies_initial_bindingSoundness' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.GraphRuntime.runPolicies_initial_bindingSoundness
