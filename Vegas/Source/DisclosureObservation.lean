/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.DisclosurePosterior

/-! # Effective disclosure recall is determined by source observations

A permanent publication cell identifies the effective disclosure bit, including
when the original intention was rejected by a guard. The functions here read
existing observations and reconstruct that effective own-action list. They do
not add information to a player or change the source's action semantics.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}
  {who : Player} {Γ : SourceCtx Player L}

/-- Carry the compressed recall over a binding. The actual binding remains an
ordinary source action; only prior disclosure intentions can be compressed. -/
def bindingRecall (name : VarId) (owner : Player) (payload : L.Ty)
    (recall : DecisionView who Γ → List (OwnAction Player L))
    (view : DecisionView who ((name, .commitment owner payload) :: Γ)) :
    List (OwnAction Player L) :=
  let own := decide (owner = who)
  recall (view.back own) ++ if own then view.2.getLast?.toList else []

/-- The effective reveal bit is read from the permanent public result cell.
No original policy, posterior, hidden binding, or registry is consulted. -/
def publicationRecall (published name : VarId) (owner : Player) (payload : L.Ty)
    (recall : DecisionView who Γ → List (OwnAction Player L))
    (view : DecisionView who ((published, .publication payload) :: Γ)) :
    List (OwnAction Player L) :=
  let own := decide (owner = who)
  recall (view.back own) ++ if own then
    [.reveal owner name (match view.1.cells.get .here with
      | .failure => false
      | .success _ => true)] else []

theorem bindingRecall_successor {payload : L.Ty} (name : VarId) (owner : Player)
    (guard : SourceGuard L Γ owner name payload) (config : Config Player L Γ)
    (recall : DecisionView who Γ → List (OwnAction Player L))
    (binding : PublicationResult (L.Val payload)) :
    bindingRecall name owner payload recall ((commitSuccessor name guard config binding).view who) =
      recall (config.view who) ++
        if owner = who then [.commit owner name payload binding] else [] := by
  simp only [bindingRecall, back_commit_view]
  by_cases own : owner = who
  · subst who
    simp only [decide_true, ite_true, Config.view, commitSuccessor, Function.update_self,
      List.getLast?_concat, Option.toList_some]
  · simp only [own, decide_false, Bool.false_eq_true, ite_false]

theorem publicationRecall_successor {payload : L.Ty} {name : VarId}
    (published : VarId) (owner : Player)
    (selected : HasVar Γ name (.commitment owner payload)) (config : Config Player L Γ)
    (recall : DecisionView who Γ → List (OwnAction Player L)) (disclose : Bool) :
    publicationRecall published name owner payload recall
        ((revealSuccessor published selected config disclose).view who) =
      recall (config.view who) ++ if owner = who then
        [.reveal owner name (effectiveDisclosure published selected config disclose)] else [] := by
  simp only [publicationRecall, back_reveal_view]
  by_cases own : owner = who
  · subst who
    simp only [decide_true, ite_true]
    have seen : ((revealSuccessor published selected config disclose).view owner).1.cells.get
        (HasVar.here : HasVar ((published, .publication payload) :: Γ) published
          (.publication payload)) = disclosureResult published selected config disclose :=
      sourceObserve_publication owner _ .here
    erw [seen]
    simp only [effectiveDisclosure]
    cases disclosureResult published selected config disclose <;> rfl
  · simp only [own, decide_false, Bool.false_eq_true, ite_false]

/-- The original guarded successor, after observation-defined recall
compression, is exactly the successor of the effective source action. -/
theorem publicationRecall_own_successor {payload : L.Ty} {name : VarId}
    (published : VarId) (selected : HasVar Γ name (.commitment who payload))
    (config : Config Player L Γ)
    (recall : DecisionView who Γ → List (OwnAction Player L)) (disclose : Bool) :
    (revealSuccessor published selected config disclose).withOwnHistory who
        (publicationRecall published name who payload recall
          ((revealSuccessor published selected config disclose).view who)) =
      revealSuccessor published selected
        (config.withOwnHistory who (recall (config.view who)))
        (effectiveDisclosure published selected config disclose) := by
  rw [publicationRecall_successor, ite_eq_left rfl, revealSuccessor_withOwnHistory]
  exact (revealSuccessor_effective_withOwnHistory published selected config disclose _).symm

theorem bindingRecall_own_successor {payload : L.Ty} (name : VarId)
    (guard : SourceGuard L Γ who name payload) (config : Config Player L Γ)
    (recall : DecisionView who Γ → List (OwnAction Player L))
    (binding : PublicationResult (L.Val payload)) :
    (commitSuccessor name guard config binding).withOwnHistory who
        (bindingRecall name who payload recall
          ((commitSuccessor name guard config binding).view who)) =
      commitSuccessor name guard
        (config.withOwnHistory who (recall (config.view who))) binding := by
  rw [bindingRecall_successor, ite_eq_left rfl, commitSuccessor_withOwnHistory]

private theorem conditional_fst_support {A B : Type*} (law : FinDist (A × B)) (value : A)
    (reached : value ∈ (law.map Prod.fst).support) (pair : A × B)
    (member : pair ∈ (law.condOnFibre Prod.fst value).support) :
    pair ∈ law.support ∧ pair.1 = value := by
  classical
  obtain ⟨witness, supported, same⟩ := FinDist.support_map .. ▸ reached
  have meets : ∃ pair ∈ Prod.fst ⁻¹' {value}, pair ∈ law.support := ⟨witness, same, supported⟩
  rw [FinDist.condOnFibre, dite_eq_left meets] at member
  exact ⟨(FinDist.support_condOn _ _ _ member).2,
    (FinDist.support_condOn _ _ _ member).1⟩

/-- Conditioning on an emitted binding preserves the information retraction:
every original intention in the posterior has that same compressed recall. -/
theorem bindingMemoryLaw_recall {payload : L.Ty} (name : VarId)
    (guard : SourceGuard L Γ who name payload) (config : Config Player L Γ)
    (remember : DecisionView who Γ → FinDist (List (OwnAction Player L)))
    (recall : DecisionView who Γ → List (OwnAction Player L))
    (choose : DecisionView who Γ → FinDist (PublicationResult (L.Val payload)))
    (coherent : ∀ past ∈ (remember (config.view who)).support,
      recall (sourceObserve who config.state, past) = config.history who)
    (binding : PublicationResult (L.Val payload))
    (reached : binding ∈ ((bindingMemoryLaw name payload remember choose
      (config.view who)).map Prod.fst).support)
    (past : List (OwnAction Player L))
    (remembered : past ∈ (((bindingMemoryLaw name payload remember choose
      (config.view who)).condOnFibre Prod.fst binding).map Prod.snd).support) :
    bindingRecall name who payload recall
        (((commitSuccessor name guard config binding).withOwnHistory who past).view who) =
      (commitSuccessor name guard config binding).history who := by
  obtain ⟨pair, conditional, rfl⟩ := FinDist.support_map .. ▸ remembered
  obtain ⟨produced, emitted⟩ := conditional_fst_support _ binding reached pair conditional
  obtain ⟨original, prior, chosen⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ produced)
  obtain ⟨value, _chosen, rfl⟩ := FinDist.support_map .. ▸ chosen
  dsimp only at emitted
  subst binding
  rw [← commitSuccessor_withOwnHistory, bindingRecall_successor, ite_eq_left rfl,
    Config.withOwnHistory_view, coherent original prior]
  simp only [commitSuccessor, Function.update_self]

/-- A rejected original disclosure and withholding occupy the same compressed
information fiber. The posterior still retains which intention was chosen. -/
theorem disclosureMemoryLaw_recall {payload : L.Ty} {name : VarId}
    (published : VarId) (selected : HasVar Γ name (.commitment who payload))
    (config : Config Player L Γ)
    (remember : DecisionView who Γ → FinDist (List (OwnAction Player L)))
    (recall : DecisionView who Γ → List (OwnAction Player L))
    (choose : DecisionView who Γ → FinDist Bool)
    (coherent : ∀ past ∈ (remember (config.view who)).support,
      recall (sourceObserve who config.state, past) = config.history who)
    (disclose : Bool)
    (reached : disclose ∈ ((disclosureMemoryLaw published selected config.registry
      config.revelations remember choose (config.view who)).map Prod.fst).support)
    (past : List (OwnAction Player L))
    (remembered : past ∈ (((disclosureMemoryLaw published selected config.registry
      config.revelations remember choose (config.view who)).condOnFibre Prod.fst disclose).map
        Prod.snd).support) :
    publicationRecall published name who payload recall
        (((revealSuccessor published selected config disclose).withOwnHistory who past).view who) =
      (revealSuccessor published selected config disclose).history who := by
  obtain ⟨pair, conditional, rfl⟩ := FinDist.support_map .. ▸ remembered
  obtain ⟨produced, emitted⟩ := conditional_fst_support _ disclose reached pair conditional
  obtain ⟨original, prior, chosen⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ produced)
  obtain ⟨intended, _chosen, rfl⟩ := FinDist.support_map .. ▸ chosen
  have effective : effectiveDisclosure published selected config intended = disclose := by
    simpa only [Config.view, effectiveDisclosureView_observe] using emitted
  rw [← effective, revealSuccessor_effective_withOwnHistory,
    ← revealSuccessor_withOwnHistory, publicationRecall_successor, ite_eq_left rfl,
    Config.withOwnHistory_view, coherent original prior]
  have unchanged : effectiveDisclosure published selected (config.withOwnHistory who original)
      intended = effectiveDisclosure published selected config intended :=
    effectiveDisclosure_observation_congr published selected _ _ rfl rfl rfl intended
  rw [unchanged]
  simp only [revealSuccessor, Function.update_self]

variable [IExpr.ResultTypes L]

/-- Compress only private ineffective disclosure intentions at the actual
source program point. The program tag and all observed cells remain intact. -/
def ProtocolView.normalizeDisclosureRecall {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) →
    (DecisionView who Γ → List (OwnAction Player L)) →
    ProtocolView who program → ProtocolView who program
  | _, _, .ret _, recall, view => (view.1, recall view)
  | _, _, .sample _ _ _ next, recall, view =>
      view.elim (fun current => .inl (current.1, recall current))
        (fun later => .inr (normalizeDisclosureRecall next
          (fun current => recall (current.back false)) later))
  | _, _, .commit (payload := payload) name owner _ _ next, recall, view =>
      view.elim (fun current => .inl (current.1, recall current))
        (fun later => .inr (normalizeDisclosureRecall next
          (bindingRecall name owner payload recall) later))
  | _, _, .reveal (payload := payload) published owner name _ _ _ next, recall, view =>
      view.elim (fun current => .inl (current.1, recall current))
        (fun later => .inr (normalizeDisclosureRecall next
          (publicationRecall published name owner payload recall) later))

/-- The matching readout on existing source configurations changes exactly
one owner's action history. It is an analysis map, not an execution state. -/
def ProtocolState.normalizeDisclosureRecall {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) →
    (DecisionView who Γ → List (OwnAction Player L)) →
    ProtocolState program → ProtocolState program
  | _, _, .ret _, recall, config => config.withOwnHistory who (recall (config.view who))
  | _, _, .sample _ _ _ next, recall, state =>
      state.elim (fun config => .inl (config.withOwnHistory who (recall (config.view who))))
        (fun later => .inr (normalizeDisclosureRecall next
          (fun view => recall (view.back false)) later))
  | _, _, .commit (payload := payload) name owner _ _ next, recall, state =>
      state.elim (fun config => .inl (config.withOwnHistory who (recall (config.view who))))
        (fun later => .inr (normalizeDisclosureRecall next
          (bindingRecall name owner payload recall) later))
  | _, _, .reveal (payload := payload) published owner name _ _ _ next, recall, state =>
      state.elim (fun config => .inl (config.withOwnHistory who (recall (config.view who))))
        (fun later => .inr (normalizeDisclosureRecall next
          (publicationRecall published name owner payload recall) later))

/-- Every compressed focal observation is a function of its original source
observation. In particular, the construction cannot split a source information
set according to a hidden guard input or another player's private history. -/
theorem ProtocolState.observe_normalizeDisclosureRecall {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) →
    (recall : DecisionView who Γ → List (OwnAction Player L)) →
    (state : ProtocolState program) →
    observe who program (normalizeDisclosureRecall program recall state) =
      ProtocolView.normalizeDisclosureRecall program recall (observe who program state)
  | _, _, .ret _, _, _ => Config.withOwnHistory_view ..
  | _, _, .sample _ _ _ next, recall, state => by
      cases state with
      | inl config => exact congrArg Sum.inl (Config.withOwnHistory_view ..)
      | inr later =>
          exact congrArg Sum.inr
            (observe_normalizeDisclosureRecall next (fun view => recall (view.back false)) later)
  | _, _, .commit (payload := payload) name owner _ _ next, recall, state => by
      cases state with
      | inl config => exact congrArg Sum.inl (Config.withOwnHistory_view ..)
      | inr later =>
          exact congrArg Sum.inr
            (observe_normalizeDisclosureRecall next (bindingRecall name owner payload recall) later)
  | _, _, .reveal (payload := payload) published owner name _ _ _ next, recall, state => by
      cases state with
      | inl config => exact congrArg Sum.inl (Config.withOwnHistory_view ..)
      | inr later =>
          exact congrArg Sum.inr
            (observe_normalizeDisclosureRecall next
              (publicationRecall published name owner payload recall) later)

/-- Other players cannot observe the private recall being compressed. This
retains their entire existing source view, not only its public component. -/
theorem ProtocolState.foreign_observe_normalizeDisclosureRecall {who : Player}
    (other : Player) (different : other ≠ who) :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) →
    (recall : DecisionView who Γ → List (OwnAction Player L)) →
    (state : ProtocolState program) →
    observe other program (normalizeDisclosureRecall program recall state) =
      observe other program state
  | _, _, .ret _, _, _ => Config.withOwnHistory_foreign_view _ other different _
  | _, _, .sample _ _ _ next, recall, state => by
      cases state with
      | inl config =>
          exact congrArg Sum.inl (Config.withOwnHistory_foreign_view _ other different _)
      | inr later =>
          exact congrArg Sum.inr (foreign_observe_normalizeDisclosureRecall other different next
            (fun view => recall (view.back false)) later)
  | _, _, .commit (payload := payload) name owner _ _ next, recall, state => by
      cases state with
      | inl config =>
          exact congrArg Sum.inl (Config.withOwnHistory_foreign_view _ other different _)
      | inr later =>
          exact congrArg Sum.inr (foreign_observe_normalizeDisclosureRecall other different next
            (bindingRecall name owner payload recall) later)
  | _, _, .reveal (payload := payload) published owner name _ _ _ next, recall, state => by
      cases state with
      | inl config =>
          exact congrArg Sum.inl (Config.withOwnHistory_foreign_view _ other different _)
      | inr later =>
          exact congrArg Sum.inr (foreign_observe_normalizeDisclosureRecall other different next
            (publicationRecall published name owner payload recall) later)

end Vegas.SourceProgram
