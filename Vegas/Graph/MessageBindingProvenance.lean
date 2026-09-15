/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Graph.MessageServiceCompletion
import Vegas.Graph.MessageVerification
import Vegas.Graph.BindingDiscipline

/-! # Origin-indexed provenance of sealed graph bindings -/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory.Math.Probability Interaction Graph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [R : IExpr.ResultTypes L]
variable {Δ : VCtx Player L}

/-- Every sealed cell is either the canonical failure encoding for its declared
origin payload, or has an owner-correct handle verifying its exact typed raw
cell. Context-name uniqueness makes lookup preservation compositional. -/
def State.BindingProvenance (origins : VarId → Option L.Ty) : State Player L Δ → Prop
  | @State.running _ _ _ _ _ context _ ideal _ bindings candidates _ _ _ =>
      (context.map Prod.fst).Nodup ∧
      ∀ {name owner ty} (source : HasVar context name (.sealed owner ty)),
        (∃ payload, origins name = some payload ∧
          Raw.mk ty (ideal.get source) = Raw.mk (R.result payload)
            ((R.valueEquiv payload).symm .failure)) ∨
        ∃ handle, lookupBinding bindings name = some handle ∧ handle.1 = owner ∧
          candidates.verify handle ⟨ty, ideal.get source⟩ = true

/-- The graph cursor and its sealed cells agree on one evolving origin map. -/
def State.DisciplinedBindingProvenance : State Player L Δ → Prop
  | @State.running _ _ _ _ _ _context graph ideal values bindings candidates
      pc clock enteredAt =>
      ∃ origins, graph.BindingDiscipline origins ∧
        State.BindingProvenance origins
          (State.running graph ideal values bindings candidates pc clock enteredAt)

/-- A cell known to have a successful value cannot be in the canonical-failure
case of origin-indexed provenance. -/
theorem State.verified_of_bindingProvenance_success
    (origins : Graph.BindingOrigins L) {context : VCtx Player L}
    (graph : Graph Player L context Δ) (ideal : VEnv L context)
    (values : PublicValues context) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L))
    (pc clock enteredAt : Nat) {name : VarId} {owner : Player} {payload : L.Ty}
    {value : L.Val payload}
    (source : HasVar context name (.sealed owner (R.result payload)))
    (origin : origins name = some payload)
    (success : R.valueEquiv payload (ideal.get source) = .success value)
    (provenance : State.BindingProvenance origins
      (State.running graph ideal values bindings candidates pc clock enteredAt)) :
    ∃ handle, lookupBinding bindings name = some handle ∧ handle.1 = owner ∧
      candidates.verify handle ⟨R.result payload, ideal.get source⟩ = true := by
  rcases provenance.2 source with failed | verified
  · obtain ⟨other, otherOrigin, rawEq⟩ := failed
    have : other = payload := Option.some.inj (otherOrigin.symm.trans origin)
    subst other
    simp only [Raw.mk.injEq] at rawEq
    have valueEq : ideal.get source =
        (R.valueEquiv payload).symm PublicationResult.failure := eq_of_heq rawEq.2
    rw [valueEq] at success
    simp at success
  · exact verified

/-- At a disciplined resolve cursor, every successfully decoded source cell has
an owner-correct accepted handle which verifies that exact cell. -/
theorem State.resolveSource_verified
    {context : VCtx Player L} {output binding : VarId} {owner : Player}
    {payload : L.Ty} (fresh : output ∉ context.map Prod.fst)
    (source : HasVar context binding (.sealed owner (R.result payload)))
    (checks : List (GuardCheck ((output, .pub (R.result payload)) :: context)))
    (tail : Graph Player L ((output, .pub (R.result payload)) :: context) Δ)
    (ideal : VEnv L context) (values : PublicValues context)
    (bindings : Bindings Player) (candidates : CommitmentCandidates Player Slot (Raw L))
    (pc clock enteredAt : Nat) {value : L.Val payload}
    (success : R.valueEquiv payload (ideal.get source) = .success value)
    (provenance : (State.running (.resolve output owner binding fresh source checks tail)
      ideal values bindings candidates pc clock enteredAt).DisciplinedBindingProvenance) :
    ∃ handle, lookupBinding bindings binding = some handle ∧ handle.1 = owner ∧
      candidates.verify handle ⟨R.result payload, ideal.get source⟩ = true := by
  obtain ⟨origins, discipline, cells⟩ := provenance
  rcases cells.2 source with ⟨origin, originAt, rawEq⟩ | verified
  · have payloadEq := discipline.1 origin originAt
    subst origin
    simp only [Raw.mk.injEq] at rawEq
    have valueEq : ideal.get source =
        (R.valueEquiv payload).symm PublicationResult.failure := eq_of_heq rawEq.2
    rw [valueEq] at success
    simp at success
  · exact verified

theorem State.initial_bindingProvenance {Γ : VCtx Player L}
    (origins : VarId → Option L.Ty) (graph : Graph Player L Γ Δ)
    (input : VEnv L Γ) (unique : (Γ.map Prod.fst).Nodup) :
    (State.initial graph input).BindingProvenance origins := by
  refine ⟨unique, ?_⟩
  intro name owner ty source
  obtain ⟨binding, verified⟩ := State.initial_binding graph input unique source
  exact Or.inr ⟨(owner, .initial name), binding, rfl, verified⟩

omit [DecidableEq Player] R in
private theorem verify_typedRaw_of_as?_eq_some
    (candidates : CommitmentCandidates Player Slot (Raw L)) (handle : Handle Player)
    (raw : Raw L) (ty : L.Ty) (value : L.Val ty)
    (verified : candidates.verify handle raw = true)
    (typed : raw.as? ty = some value) :
    candidates.verify handle ⟨ty, value⟩ = true := by
  obtain ⟨rawTy, rawValue⟩ := raw
  simp only [Raw.as?] at typed
  split at typed
  · rename_i same
    subst rawTy
    simp only [Option.some.injEq] at typed
    cases typed
    exact verified
  · contradiction

private theorem privateStep_bindingProvenance (runtime : GraphRuntime Player L Δ)
    (origins : VarId → Option L.Ty) (state : State Player L Δ)
    (who : Player) (command : PrivateCommand L)
    (provenance : state.BindingProvenance origins) :
    (runtime.privateStep state who command).BindingProvenance origins := by
  cases state with
  | running graph ideal values bindings candidates pc clock enteredAt =>
      rcases provenance with ⟨unique, provenance⟩
      cases command with
      | rememberDisclosure => exact ⟨unique, provenance⟩
      | prepare slot raw =>
          refine ⟨unique, ?_⟩
          intro name owner ty source
          rcases provenance source with failed | ⟨handle, binding, handleOwner, verified⟩
          · exact Or.inl failed
          · refine Or.inr ⟨handle, binding, handleOwner, ?_⟩
            have lookup := (candidates.verify_eq_true_iff handle
              ⟨ty, ideal.get source⟩).mp verified
            apply (CommitmentCandidates.verify_eq_true_iff ..).mpr
            rw [candidates.lookup_prepare_eq_of_not_fresh handle who (.prepared slot) raw
              (by rw [lookup]; simp), lookup]

private theorem extendPublic_bindingProvenance
    (origins : VarId → Option L.Ty) {context : VCtx Player L}
    {name : VarId} {ty : L.Ty} (fresh : name ∉ context.map Prod.fst)
    (current : Graph Player L context Δ)
    (next : Graph Player L ((name, .pub ty) :: context) Δ)
    (value : L.Val ty) (ideal : VEnv L context) (values : PublicValues context)
    (bindings : Bindings Player) (candidates : CommitmentCandidates Player Slot (Raw L))
    (pc clock enteredAt : Nat)
    (provenance : (State.running current ideal values bindings candidates
      pc clock enteredAt).BindingProvenance origins) :
    (State.running next (VEnv.cons value ideal) (PublicValues.consPublic value values)
      bindings candidates (pc + 1) clock enteredAt).BindingProvenance origins := by
  rcases provenance with ⟨unique, provenance⟩
  refine ⟨List.nodup_cons.mpr ⟨fresh, unique⟩, ?_⟩
  intro field owner cellTy source
  cases source with
  | there source =>
      simpa [VEnv.cons, VEnv.get] using provenance source

private theorem advanceBindFailure_bindingProvenance
    (origins : VarId → Option L.Ty) {context : VCtx Player L}
    {name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : name ∉ context.map Prod.fst)
    (next : Graph Player L ((name, .sealed owner (R.result payload)) :: context) Δ)
    (ideal : VEnv L context) (values : PublicValues context)
    (bindings : Bindings Player) (candidates : CommitmentCandidates Player Slot (Raw L))
    (pc clock enteredAt : Nat)
    (provenance : (State.running (.bind name owner fresh next) ideal values
      bindings candidates pc clock enteredAt).BindingProvenance origins) :
    (advanceBindFailure next ideal values bindings candidates pc clock).BindingProvenance
      (Graph.BindingOrigins.insert origins name payload) := by
  rcases provenance with ⟨unique, provenance⟩
  refine ⟨List.nodup_cons.mpr ⟨fresh, unique⟩, ?_⟩
  intro field fieldOwner cellTy source
  cases source with
  | here => exact Or.inl ⟨payload, by simp, by simp [VEnv.cons, VEnv.get]⟩
  | there source =>
      rcases provenance source with ⟨other, otherOrigin, rawEq⟩ | verified
      · refine Or.inl ⟨other, ?_, ?_⟩
        · rw [Graph.BindingOrigins.insert_other origins payload]
          · exact otherOrigin
          · intro same
            exact fresh (same.symm ▸ source.mem_map_fst)
        · simpa [advanceBindFailure, VEnv.cons, VEnv.get] using rawEq
      · exact Or.inr (by simpa [advanceBindFailure, VEnv.cons, VEnv.get] using verified)

private theorem advanceBind_bindingProvenance
    (origins : VarId → Option L.Ty) {context : VCtx Player L}
    {name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : name ∉ context.map Prod.fst)
    (next : Graph Player L ((name, .sealed owner (R.result payload)) :: context) Δ)
    (ideal : VEnv L context) (values : PublicValues context)
    (bindings : Bindings Player) (candidates : CommitmentCandidates Player Slot (Raw L))
    (pc clock enteredAt : Nat) (accepted : Handle Player) (handleOwner : accepted.1 = owner)
    (provenance : (State.running (.bind name owner fresh next) ideal values bindings
      candidates pc clock enteredAt).BindingProvenance origins) :
    (advanceBind next ideal values bindings candidates pc clock accepted).BindingProvenance
      (Graph.BindingOrigins.insert origins name payload) := by
  rcases provenance with ⟨unique, provenance⟩
  refine ⟨List.nodup_cons.mpr ⟨fresh, unique⟩, ?_⟩
  intro field fieldOwner cellTy source
  cases source with
  | here =>
      simp only [VEnv.cons, VEnv.get]
      cases lookup : candidates.lookup accepted with
      | fresh => exact Or.inl ⟨payload, by simp, rfl⟩
      | unopenable => exact Or.inl ⟨payload, by simp, rfl⟩
      | openable raw =>
          cases typed : raw.as? (R.result payload) with
          | none => exact Or.inl ⟨payload, by simp, by simp [typed]⟩
          | some encoded =>
              simp only [typed, Option.getD_some]
              refine Or.inr ⟨accepted, by simp [lookupBinding], handleOwner, ?_⟩
              rw [candidates.verify_accept]
              apply verify_typedRaw_of_as?_eq_some candidates accepted raw
                (R.result payload) encoded
              · exact (CommitmentCandidates.verify_eq_true_iff ..).mpr lookup
              · exact typed
  | there source =>
      rcases provenance source with failed | ⟨handle, binding, ownerEq, verified⟩
      · obtain ⟨other, otherOrigin, rawEq⟩ := failed
        refine Or.inl ⟨other, ?_, ?_⟩
        · rw [Graph.BindingOrigins.insert_other origins payload]
          · exact otherOrigin
          · intro same
            exact fresh (same.symm ▸ source.mem_map_fst)
        · simpa [advanceBind, VEnv.cons, VEnv.get] using rawEq
      · refine Or.inr ⟨handle, ?_, ownerEq, ?_⟩
        · have different : name ≠ field := by
            intro same
            exact fresh (same ▸ source.mem_map_fst)
          simpa [lookupBinding, different] using binding
        · rw [candidates.verify_accept]
          simpa [advanceBind, VEnv.cons, VEnv.get] using verified

theorem State.initial_disciplinedBindingProvenance {Γ : VCtx Player L}
    (graph : Graph Player L Γ Δ) (input : VEnv L Γ)
    (unique : (Γ.map Prod.fst).Nodup)
    (discipline : graph.BindingDiscipline Graph.BindingOrigins.none) :
    (State.initial graph input).DisciplinedBindingProvenance := by
  exact ⟨Graph.BindingOrigins.none, discipline,
    State.initial_bindingProvenance _ graph input unique⟩

private theorem privateStep_disciplinedBindingProvenance
    (runtime : GraphRuntime Player L Δ) (state : State Player L Δ)
    (who : Player) (command : PrivateCommand L)
    (provenance : state.DisciplinedBindingProvenance) :
    (runtime.privateStep state who command).DisciplinedBindingProvenance := by
  cases state with
  | running graph ideal values bindings candidates pc clock enteredAt =>
      obtain ⟨origins, discipline, cells⟩ := provenance
      cases command with
      | prepare slot raw =>
          exact ⟨origins, discipline,
            privateStep_bindingProvenance runtime origins _ who (.prepare slot raw) cells⟩
      | rememberDisclosure disclosure =>
          exact ⟨origins, discipline, privateStep_bindingProvenance runtime origins _ who
            (.rememberDisclosure disclosure) cells⟩

private theorem handle_disciplinedBindingProvenance
    (runtime : GraphRuntime Player L Δ) (state : State Player L Δ)
    (message : Message Player (Payload Player L)) (nextState : State Player L Δ)
    (provenance : state.DisciplinedBindingProvenance)
    (accepted : runtime.handle state message = some nextState) :
    nextState.DisciplinedBindingProvenance := by
  cases state with
  | running graph ideal values bindings candidates pc clock enteredAt =>
      obtain ⟨origins, discipline, cells⟩ := provenance
      cases graph with
      | ret | sample => cases message.payload <;> simp [GraphRuntime.handle] at accepted
      | bind name owner fresh tail =>
          cases packet : message.payload <;>
            simp only [GraphRuntime.handle, packet] at accepted
          · split_ifs at accepted
            rename_i valid
            cases accepted
            simp only [Bool.and_eq_true, decide_eq_true_eq] at valid
            refine ⟨Graph.BindingOrigins.insert origins name _, discipline, ?_⟩
            exact advanceBind_bindingProvenance origins fresh tail ideal values bindings
              candidates pc clock enteredAt _ valid.2 cells
          all_goals contradiction
      | resolve output owner binding fresh source checks tail =>
          cases packet : message.payload with
          | commitment | malformed => simp [GraphRuntime.handle, packet] at accepted
          | withhold site =>
              simp only [GraphRuntime.handle, packet] at accepted
              split_ifs at accepted
              cases accepted
              exact ⟨origins, discipline.2,
                extendPublic_bindingProvenance origins fresh _ tail _ ideal values bindings
                  candidates pc clock enteredAt cells⟩
          | opening site handle raw =>
              simp only [GraphRuntime.handle, packet] at accepted
              split_ifs at accepted
              cases typed : raw.as? _ with
              | none => rw [typed] at accepted; contradiction
              | some encoded =>
                  rw [typed] at accepted
                  cases accepted
                  exact ⟨origins, discipline.2,
                    extendPublic_bindingProvenance origins fresh _ tail _ ideal values bindings
                      candidates pc clock enteredAt cells⟩

private theorem environmentStep_disciplinedBindingProvenance
    (runtime : GraphRuntime Player L Δ) (state : State Player L Δ)
    (command : EnvironmentCommand) (nextState : State Player L Δ)
    (provenance : state.DisciplinedBindingProvenance)
    (supported : nextState ∈ (runtime.environmentStep state command).support) :
    nextState.DisciplinedBindingProvenance := by
  cases command
  cases state with
  | running graph ideal values bindings candidates pc clock enteredAt =>
      obtain ⟨origins, discipline, cells⟩ := provenance
      cases graph with
      | ret =>
          simp only [environmentStep, tick, FinDist.mem_support_pure] at supported
          subst nextState
          exact ⟨origins, discipline, cells⟩
      | sample name payload law tail =>
          simp only [environmentStep, tick, FinDist.support_map, Set.mem_image] at supported
          obtain ⟨value, _, rfl⟩ := supported
          exact ⟨origins, discipline,
            extendPublic_bindingProvenance origins (by assumption)
              (.sample name payload law tail) tail value ideal values bindings candidates
              pc (clock + 1) (clock + 1) cells⟩
      | bind name owner fresh tail =>
          simp only [environmentStep, tick] at supported
          split at supported
          · simp only [FinDist.mem_support_pure] at supported
            subst nextState
            exact ⟨Graph.BindingOrigins.insert origins name _, discipline,
              advanceBindFailure_bindingProvenance origins fresh tail ideal values bindings
                candidates pc (clock + 1) enteredAt cells⟩
          · simp only [FinDist.mem_support_pure] at supported
            subst nextState
            exact ⟨origins, discipline, cells⟩
      | resolve output owner binding fresh source checks tail =>
          simp only [environmentStep, tick] at supported
          split at supported
          · simp only [FinDist.mem_support_pure] at supported
            subst nextState
            exact ⟨origins, discipline.2,
              extendPublic_bindingProvenance origins fresh
                (.resolve output owner binding fresh source checks tail) tail _ ideal values
                bindings candidates pc (clock + 1) (clock + 1) cells⟩
          · simp only [FinDist.mem_support_pure] at supported
            subst nextState
            exact ⟨origins, discipline, cells⟩

/-- Origin discipline and accepted-binding provenance survive arbitrary native
player policies, environment policies, and message scheduling. -/
theorem runPolicies_disciplinedBindingProvenance (runtime : GraphRuntime Player L Δ)
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player))
    (execution next : runtime.application.PolicyExecution)
    (provenance : execution.native.application.DisciplinedBindingProvenance)
    (supported : next ∈
      (runtime.application.runPolicies players environment schedule execution).support) :
    next.native.application.DisciplinedBindingProvenance := by
  apply runtime.application.runPolicies_application_invariant
    State.DisciplinedBindingProvenance
    (privateStep_disciplinedBindingProvenance runtime)
    (handle_disciplinedBindingProvenance runtime)
    (environmentStep_disciplinedBindingProvenance runtime)
    players environment schedule execution next provenance supported

theorem runPolicies_initial_disciplinedBindingProvenance
    {Γ : VCtx Player L} (runtime : GraphRuntime Player L Δ)
    (graph : Graph Player L Γ Δ) (input : VEnv L Γ)
    (unique : (Γ.map Prod.fst).Nodup)
    (discipline : graph.BindingDiscipline Graph.BindingOrigins.none)
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player))
    (next : runtime.application.PolicyExecution)
    (supported : next ∈ (runtime.application.runPolicies players environment schedule
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application
          (State.initial graph input)))).support) :
    next.native.application.DisciplinedBindingProvenance := by
  apply runtime.runPolicies_disciplinedBindingProvenance players environment schedule _ next
    (State.initial_disciplinedBindingProvenance graph input unique discipline) supported

end Vegas.GraphRuntime
