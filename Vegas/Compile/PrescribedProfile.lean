module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Compile.EventGraphDeviation
public import Vegas.EventGraph.CanonicalPrefix
public import Vegas.Compile.PublicationPolicy
public import Vegas.Source.BindingSubmission

@[expose] public section

/-! # Total source-prefix compilation

The prescribed compiler pads source-prefix observations and repairs binding
omissions, including at malformed callbacks. Submitting source policies already
submit at every coherent source prefix, so this repair preserves their complete
canonical configuration law under every valid dependency choice.
-/

noncomputable section

namespace Vegas

open EventGraph SourceProgram GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Submission rules out omission at every structurally complete source prefix.
Malformed observations outside such prefixes are deliberately not covered. -/
theorem compilePolicyTable_submitted_of_prefix
    {wholeΓ : SourceCtx Player L} {wholeOpen : Finset VarId}
    (whole : SourceProgram Player L wholeΓ wholeOpen) (who : Player) :
    ∀ {Γ : SourceCtx Player L} {openNames : Finset VarId}
      (program : SourceProgram Player L Γ openNames)
      (refs : ContextRefs (graphLayout whole) Γ)
      (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole) program)
      (_before : ContextRefsBefore refs embedding)
      (policy : BehavioralPolicy who program) (_submits : SourceProgram.SubmitsBindings program
        policy)
      (index : Fin (eventCount program)) (config : (toInformationGraph whole).Config)
      (_ordered : config.cut.IsPrefix (embedding.event index).val)
      (_owned : eventOwner? program index = some who) (_active : who ∉ config.defaulted)
      (history : List (OwnAction Player L)) (action : (outputLayout program index).Action)
      (_supported : action ∈ (compilePolicyTable program refs embedding.ref who policy index
        ((toInformationGraph whole).playerStore who config.store) config.defaults history).support),
      (outputLayout program index).Submitted action := by
  intro Γ openNames program
  induction program with
  | ret payoffs =>
      intro refs embedding before policy submits index
      exact nomatch index
  | @sample Γ openNames name payload fresh law next ih =>
      intro refs embedding before policy submits index config ordered owned active history action
        supported
      cases index using Fin.cases with
      | zero => trivial
      | succ tail =>
          let head : FieldRef (graphLayout whole) (.publicData payload) := by
            simpa [outputLayout, eventCount] using embedding.ref ⟨0, by simp [eventCount]⟩
          let tailEmbedding := embedding.tail next (by simp [eventCount]) (fun _ => rfl)
          have tailBefore : ContextRefsBefore (refs.cons head) tailEmbedding :=
            before.tail_cons next (by simp [eventCount]) (fun _ => rfl) head rfl
          have outputsEq : (fun remaining => embedding.ref (Fin.succ remaining)) =
              tailEmbedding.ref := by
            funext remaining
            rfl
          refine ih (refs.cons head) tailEmbedding tailBefore policy submits tail config
            ?_ owned active history action ?_
          · simpa [tailEmbedding, OutputEmbedding.tail] using ordered
          · rw [← outputsEq]
            simpa only [compilePolicyTable, Fin.cases_succ, head] using supported
  | @commit Γ openNames name owner payload fresh guard next ih =>
      intro refs embedding before policy submits index config ordered owned active history action
        supported
      cases index using Fin.cases with
      | zero =>
          have same : owner = who := Option.some.inj owned
          have activeDefaults : who ∉ config.defaults.defaulted := active
          obtain ⟨observation, decoded⟩ := exists_decodeObservation_of_prefix whole refs embedding
            before ⟨0, by simp [eventCount]⟩ _ config ordered rfl who
          have chosen : action ∈ (policy.1 same
              ⟨observation, config.defaults, history⟩ active).support := by
            simpa only [compilePolicyTable, Fin.cases_zero, dite_eq_right activeDefaults,
              dite_eq_left same, decoded] using supported
          cases action with
          | none => exact (submits.1 same ⟨observation, config.defaults, history⟩
              activeDefaults chosen).elim
          | some value => trivial
      | succ tail =>
          let head : FieldRef (graphLayout whole) (.binding owner payload) := by
            simpa [outputLayout, eventCount] using embedding.ref ⟨0, by simp [eventCount]⟩
          let tailEmbedding := embedding.tail next (by simp [eventCount]) (fun _ => rfl)
          have tailBefore : ContextRefsBefore (refs.cons head) tailEmbedding :=
            before.tail_cons next (by simp [eventCount]) (fun _ => rfl) head rfl
          have outputsEq : (fun remaining => embedding.ref (Fin.succ remaining)) =
              tailEmbedding.ref := by
            funext remaining
            rfl
          refine ih (refs.cons head) tailEmbedding tailBefore policy.2 submits.2 tail config
            ?_ owned active history action ?_
          · simpa [tailEmbedding, OutputEmbedding.tail] using ordered
          · rw [← outputsEq]
            simpa only [compilePolicyTable, Fin.cases_succ, head] using supported
  | @reveal Γ openNames published owner name payload fresh selected unresolved next ih =>
      intro refs embedding before policy submits index config ordered owned active history action
        supported
      cases index using Fin.cases with
      | zero => trivial
      | succ tail =>
          let head : FieldRef (graphLayout whole) (.publication payload) := by
            simpa [outputLayout, eventCount] using embedding.ref ⟨0, by simp [eventCount]⟩
          let tailEmbedding := embedding.tail next (by simp [eventCount]) (fun _ => rfl)
          have tailBefore : ContextRefsBefore (refs.cons head) tailEmbedding :=
            before.tail_cons next (by simp [eventCount]) (fun _ => rfl) head rfl
          have outputsEq : (fun remaining => embedding.ref (Fin.succ remaining)) =
              tailEmbedding.ref := by
            funext remaining
            rfl
          refine ih (refs.cons head) tailEmbedding tailBefore policy.2 submits tail config
            ?_ owned active history action ?_
          · simpa [tailEmbedding, OutputEmbedding.tail] using ordered
          · rw [← outputsEq]
            simpa only [compilePolicyTable, Fin.cases_succ, head] using supported

/-- The unmodified compiler submits at every active canonical source-prefix callback. -/
theorem compileEventPolicy_submitted_of_prefix {Γ : SourceCtx Player L}
    {openNames : Finset VarId} (program : SourceProgram Player L Γ openNames)
    (who : Player) (policy : BehavioralPolicy who program) (submits : SourceProgram.SubmitsBindings
      program policy)
    (event : (toInformationGraph program).EventId)
    (config : (toInformationGraph program).Config) (ordered : config.cut.IsPrefix event.val)
    (actor : (toInformationGraph program).actor? event = some who)
    (active : who ∉ config.defaulted) (action : (toInformationGraph program).Action event)
    (supported : action ∈ (compileEventPolicy program who policy event actor
      ((toInformationGraph program).playerObserve who config) active).support) :
    ((toInformationGraph program).outputLayout event).Submitted action := by
  apply compilePolicyTable_submitted_of_prefix program who program _ (outputEmbedding program)
    (initialRefsBefore program) policy submits event config ordered
    ((eventOwner?_eq_actor program event).trans actor) active
    (decodeCompletions program ((toInformationGraph program).playerObserve who config).ownActions)
    action
  have outputsEq : (outputEmbedding program).ref = outputRef program := by
    funext index
    rfl
  rw [outputsEq]
  exact supported

/-- Repairing a compiled policy changes nothing at a complete source prefix. -/
theorem compileEventPolicy_submit_eq_of_prefix {Γ : SourceCtx Player L}
    {openNames : Finset VarId} (program : SourceProgram Player L Γ openNames)
    (who : Player) (policy : BehavioralPolicy who program) (submits : SourceProgram.SubmitsBindings
      program policy)
    (event : (toInformationGraph program).EventId)
    (config : (toInformationGraph program).Config) (ordered : config.cut.IsPrefix event.val)
    (actor : (toInformationGraph program).actor? event = some who)
    (active : who ∉ config.defaulted) :
    (toInformationGraph program).submitPolicy who (compileEventPolicy program who policy)
        event actor ((toInformationGraph program).playerObserve who config) active =
      compileEventPolicy program who policy event actor
        ((toInformationGraph program).playerObserve who config) active := by
  unfold submitPolicy
  calc
    _ = (compileEventPolicy program who policy event actor
        ((toInformationGraph program).playerObserve who config) active).map id := by
      apply map_congr_on_support
      intro action supported
      exact EventField.submitAction_eq_self _ _
        (compileEventPolicy_submitted_of_prefix program who policy submits event config ordered
          actor active action supported)
    _ = _ := PMF.map_id _

/-- Repairing malformed binding callbacks preserves the full canonical configuration law. -/
private theorem runPolicies_canonical_submit_compile_information {Γ : SourceCtx Player L}
    {openNames : Finset VarId} (program : SourceProgram Player L Γ openNames)
    (profile : BehavioralProfile program) (submits : ∀ who, SourceProgram.SubmitsBindings program
      (profile who))
    (inputs : (toInformationGraph program).Inputs) :
    (toInformationGraph program).runPolicies (toInformationGraph program).canonicalScheduler
        ((toInformationGraph program).submitProfile (compileEventProfile program profile)) inputs =
      (toInformationGraph program).runPolicies (toInformationGraph program).canonicalScheduler
        (compileEventProfile program profile) inputs := by
  apply runPolicies_canonical_eq_of_reachable
  intro config _reachable offset ordered event _ready rank who actor active
  apply compileEventPolicy_submit_eq_of_prefix program who _ (submits who) event config
    (rank ▸ ordered) actor active

/-- The same canonical repair law holds against any one graph policy replacement. -/
private theorem runPolicies_canonical_submit_compile_update_information {Γ : SourceCtx Player L}
    {openNames : Finset VarId} (program : SourceProgram Player L Γ openNames)
    (profile : BehavioralProfile program) (who : Player)
    (submits : ∀ owner, owner ≠ who → SourceProgram.SubmitsBindings program (profile owner))
    (policy : (toInformationGraph program).BehavioralPolicy who)
    (inputs : (toInformationGraph program).Inputs) :
    (toInformationGraph program).runPolicies (toInformationGraph program).canonicalScheduler
        (Profile.update (sig := (toInformationGraph program).gameSignature)
          ((toInformationGraph program).submitProfile (compileEventProfile program profile))
          who policy) inputs =
      (toInformationGraph program).runPolicies (toInformationGraph program).canonicalScheduler
        (Profile.update (sig := (toInformationGraph program).gameSignature)
          (compileEventProfile program profile) who policy) inputs := by
  apply runPolicies_canonical_eq_of_reachable
  intro config _reachable offset ordered event _ready rank owner actor active
  by_cases same : owner = who
  · subst owner
    simp only [Profile.update_same]
  · simp only [Profile.update_of_ne _ _ same]
    exact compileEventPolicy_submit_eq_of_prefix program owner _ (submits owner same) event config
      (rank ▸ ordered) actor active

/-- Repairing compiled bindings preserves the full canonical law for every dependency choice. -/
theorem runPolicies_canonical_submit_compile {Γ : SourceCtx Player L}
    {openNames : Finset VarId} (program : SourceProgram Player L Γ openNames)
    (deps : (toEventGraph program).Dependencies) (profile : BehavioralProfile program)
    (submits : ∀ who, SourceProgram.SubmitsBindings program (profile who))
    (inputs : ((toEventGraph program).withDependencies deps).Inputs) :
    ((toEventGraph program).withDependencies deps).runPolicies
        ((toEventGraph program).withDependencies deps).canonicalScheduler
        (((toEventGraph program).withDependencies deps).submitProfile
          (compileEventProfile program profile)) inputs =
      ((toEventGraph program).withDependencies deps).runPolicies
        ((toEventGraph program).withDependencies deps).canonicalScheduler
        (compileEventProfile program profile) inputs := by
  let graph := (toEventGraph program).withDependencies deps
  calc
    _ = ((toInformationGraph program).runPolicies (toInformationGraph program).canonicalScheduler
        ((toInformationGraph program).submitProfile (compileEventProfile program profile))
          inputs).map
          graph.fromSequentialConfig :=
      (canonical_fromSequential_config_law graph _ inputs).symm
    _ = ((toInformationGraph program).runPolicies (toInformationGraph program).canonicalScheduler
        (compileEventProfile program profile) inputs).map graph.fromSequentialConfig := by
      rw [runPolicies_canonical_submit_compile_information program profile submits inputs]
    _ = _ := canonical_fromSequential_config_law graph _ inputs

/-- Canonical repair preserves the full law against any graph-policy replacement,
for every dependency choice. The replacement need not submit or disclose. -/
theorem runPolicies_canonical_submit_compile_update {Γ : SourceCtx Player L}
    {openNames : Finset VarId} (program : SourceProgram Player L Γ openNames)
    (deps : (toEventGraph program).Dependencies) (profile : BehavioralProfile program)
    (who : Player) (submits : ∀ owner, owner ≠ who → SourceProgram.SubmitsBindings program (profile
      owner))
    (policy : ((toEventGraph program).withDependencies deps).BehavioralPolicy who)
    (inputs : ((toEventGraph program).withDependencies deps).Inputs) :
    ((toEventGraph program).withDependencies deps).runPolicies
        ((toEventGraph program).withDependencies deps).canonicalScheduler
        (Profile.update (sig := ((toEventGraph program).withDependencies deps).gameSignature)
          (((toEventGraph program).withDependencies deps).submitProfile
            (compileEventProfile program profile)) who policy) inputs =
      ((toEventGraph program).withDependencies deps).runPolicies
        ((toEventGraph program).withDependencies deps).canonicalScheduler
        (Profile.update (sig := ((toEventGraph program).withDependencies deps).gameSignature)
          (compileEventProfile program profile) who policy) inputs := by
  let graph := (toEventGraph program).withDependencies deps
  calc
    _ = ((toInformationGraph program).runPolicies (toInformationGraph program).canonicalScheduler
        (Profile.update (sig := (toInformationGraph program).gameSignature)
          ((toInformationGraph program).submitProfile (compileEventProfile program profile))
            who policy) inputs).map graph.fromSequentialConfig :=
      (canonical_fromSequential_config_law graph _ inputs).symm
    _ = ((toInformationGraph program).runPolicies (toInformationGraph program).canonicalScheduler
        (Profile.update (sig := (toInformationGraph program).gameSignature)
          (compileEventProfile program profile) who policy) inputs).map graph.fromSequentialConfig
            := by
      rw [runPolicies_canonical_submit_compile_update_information program profile who submits
        policy inputs]
    _ = _ := canonical_fromSequential_config_law graph _ inputs

/-- Source-prefix clients with total binding submissions, on any valid dependency choice. -/
def compilePrescribedProfile {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames) (deps : (toEventGraph program).Dependencies)
    (profile : BehavioralProfile program) :
    ((toEventGraph program).withDependencies deps).BehavioralProfile :=
  let graph := (toEventGraph program).withDependencies deps
  graph.submitProfile (graph.prefixProfile (compileEventProfile program profile))

/-- Every prescribed policy submits at every active binding, even at malformed callbacks. -/
theorem compilePrescribedProfile_submits {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames) (deps : (toEventGraph program).Dependencies)
    (profile : BehavioralProfile program) :
    ((toEventGraph program).withDependencies deps).SubmitsBindings
      (compilePrescribedProfile program deps profile) :=
  submitsBindings_submitProfile _ _

/-- Disclosing source policies compile to point-mass opening at every active publication. -/
theorem compilePrescribedProfile_publication {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames) (deps : (toEventGraph program).Dependencies)
    (profile : BehavioralProfile program) (disclosing : ∀ who, Disclosing program (profile who))
    (who : Player) (event : ((toEventGraph program).withDependencies deps).EventId)
    (actor : ((toEventGraph program).withDependencies deps).actor? event = some who)
    (publication : (((toEventGraph program).withDependencies deps).outputLayout
      event).IsPublication)
    (observation : ((toEventGraph program).withDependencies deps).PlayerObservation who)
    (active : who ∉ observation.defaulted) :
    compilePrescribedProfile program deps profile who event actor observation active =
      PMF.pure (EventField.openAction _ publication) := by
  unfold compilePrescribedProfile submitProfile submitPolicy prefixProfile prefixPolicy
    compileEventProfile
  rw [compileEventPolicy_publication program who _ (disclosing who) event actor publication]
  rw [PMF.pure_map]
  congr 1
  exact EventField.submitAction_eq_self _ _
    (EventField.submitted_of_publication _ publication _)

/-- Prescribed publication kernels cannot condition on observations. -/
theorem compilePrescribedProfile_oblivious {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames) (deps : (toEventGraph program).Dependencies)
    (profile : BehavioralProfile program) (disclosing : ∀ who, Disclosing program (profile who)) :
    ((toEventGraph program).withDependencies deps).ObliviousAtPublications
      (compilePrescribedProfile program deps profile) := by
  intro who event actor publication left right leftActive rightActive
  rw [compilePrescribedProfile_publication program deps profile disclosing who event actor
    publication,
    compilePrescribedProfile_publication program deps profile disclosing who event actor
      publication]

/-- A prescribed opening is the decisive alternative to refusing publication. -/
theorem compilePrescribedProfile_opensDecisively {Γ : SourceCtx Player L}
    {openNames : Finset VarId} (program : SourceProgram Player L Γ openNames)
    (deps : (toEventGraph program).Dependencies) (profile : BehavioralProfile program)
    (disclosing : ∀ who, Disclosing program (profile who)) (who : Player) :
    ((toEventGraph program).withDependencies deps).OpensDecisively who
      (compilePrescribedProfile program deps profile who) := by
  apply opensDecisively_of_opens
  intro config event actor publication active
  exact compilePrescribedProfile_publication program deps profile disclosing who event actor
    publication (((toEventGraph program).withDependencies deps).playerObserve who config) active

/-- Every dependency choice has the same full canonical prescribed law as source order,
with the additional source-order dependencies forgotten in the result. -/
theorem runPolicies_canonical_compilePrescribedProfile {Γ : SourceCtx Player L}
    {openNames : Finset VarId} (program : SourceProgram Player L Γ openNames)
    (deps : (toEventGraph program).Dependencies) (profile : BehavioralProfile program)
    (submits : ∀ who, SourceProgram.SubmitsBindings program (profile who))
    (inputs : ((toEventGraph program).withDependencies deps).Inputs) :
    ((toEventGraph program).withDependencies deps).runPolicies
        ((toEventGraph program).withDependencies deps).canonicalScheduler
        (compilePrescribedProfile program deps profile) inputs =
      ((toInformationGraph program).runPolicies (toInformationGraph program).canonicalScheduler
        (compileEventProfile program profile) inputs).map
          ((toEventGraph program).withDependencies deps).fromSequentialConfig := by
  let graph := (toEventGraph program).withDependencies deps
  change graph.runPolicies graph.canonicalScheduler
    (graph.submitProfile (graph.prefixProfile (compileEventProfile program profile))) inputs = _
  rw [submitProfile_prefixProfile,
    runPolicies_canonical_prefixProfile _ (submitsBindings_submitProfile _ _)]
  rw [runPolicies_canonical_submit_compile program deps profile submits inputs]
  exact (canonical_fromSequential_config_law graph _ inputs).symm

theorem compilePolicyTable_submitBindings {Field : Type}
    {layout : Field → EventField Player L} :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
      (refs : ContextRefs layout Γ)
      (outputs : ∀ event, FieldRef layout (outputLayout program event))
      (who : Player) (policy : BehavioralPolicy who program) (event : Fin (eventCount program))
      (store : Store layout) (defaults : DefaultHistory Player) (history : List (OwnAction Player
        L)),
      (compilePolicyTable program refs outputs who (policy.submitBindings program) event store
          defaults history).map (EventField.submitAction (outputLayout program event)) =
        (compilePolicyTable program refs outputs who policy event store defaults history).map
          (EventField.submitAction (outputLayout program event))
  | _, _, .ret _, _, _, _, _, event, _, _, _ => nomatch event
  | _, _, .sample _ _ _ next, refs, outputs, who, policy, event, store, defaults, history => by
      cases event using Fin.cases with
      | zero => rfl
      | succ tail => exact compilePolicyTable_submitBindings next _ _ who policy tail _ _ _
  | _, _, .commit _ owner _ _ next, refs, outputs, who, policy, event, store, defaults, history =>
    by
      cases event using Fin.cases with
      | zero =>
          simp only [compilePolicyTable, BehavioralPolicy.submitBindings, Fin.cases_zero]
          by_cases inactive : who ∈ defaults.defaulted
          · simp only [dite_eq_left inactive]
          · simp only [dite_eq_right inactive]
            by_cases owned : owner = who
            · simp only [dite_eq_left owned]
              cases decoded : decodeObservation? who refs store with
              | none => rfl
              | some observation =>
                  simp only [PMF.map_comp]
                  rfl
            · simp only [dite_eq_right owned]
      | succ tail => exact compilePolicyTable_submitBindings next _ _ who policy.2 tail _ _ _
  | _, _, .reveal _ _ _ _ _ _ next, refs, outputs, who, policy, event, store, defaults, history =>
    by
      cases event using Fin.cases with
      | zero => rfl
      | succ tail => exact compilePolicyTable_submitBindings next _ _ who policy.2 tail _ _ _

theorem submitProfile_compile_submitBindings {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (deps : (toEventGraph program).Dependencies)
    (profile : BehavioralProfile program) :
    ((toEventGraph program).withDependencies deps).submitProfile
        (compileEventProfile program (fun who => (profile who).submitBindings program)) =
      ((toEventGraph program).withDependencies deps).submitProfile
        (compileEventProfile program profile) := by
  funext who event actor observation active
  exact compilePolicyTable_submitBindings program _ _ who (profile who) event _ _ _

/-- Repairing source omissions leaves the prescribed graph clients identical. -/
theorem compilePrescribedProfile_submitBindings {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (deps : (toEventGraph program).Dependencies)
    (profile : BehavioralProfile program) :
    compilePrescribedProfile program deps (fun who => (profile who).submitBindings program) =
      compilePrescribedProfile program deps profile := by
  unfold compilePrescribedProfile
  simp only [submitProfile_prefixProfile]
  rw [submitProfile_compile_submitBindings program deps profile]

end Vegas
