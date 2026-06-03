import Vegas.Theorems.Graph
import Vegas.EventGraph.Batch
import Vegas.Machine.Adapter.RoundView

/-!
# EventGraph visibility facts

Player observations expose the ready commit frontier and exactly the
graph-causal field values used by those ready commit nodes.  Public
observations expose completed nodes and public available field values.
-/

namespace Vegas

variable {P : Type} {L : IExpr}

/-! ## Source-level visibility -/

/-- Payoff evaluation depends only on the public erasure of the terminal
environment. Hidden values can affect payoffs only after they have been
revealed into public state. -/
theorem evalPayoffs_eq_of_erasePubEnv_eq
    [DecidableEq P]
    {Γ : VCtx P L}
    {payoffs : List (P × L.Expr (erasePubVCtx Γ) L.int)}
    {left right : VEnv L Γ}
    (hpub : VEnv.erasePubEnv left = VEnv.erasePubEnv right) :
    evalPayoffs payoffs left = evalPayoffs payoffs right := by
  unfold evalPayoffs
  rw [hpub]

/-- Sample distributions are evaluated on the public erasure of the current
environment. There is no private-sample primitive in VegasCore. -/
theorem sample_distribution_env_eq_public_env
    {Γ : VCtx P L} (env : VEnv L Γ) :
    VEnv.eraseSampleEnv env = VEnv.erasePubEnv env := rfl

/-- The sample typing context is definitionally the public context. -/
theorem sample_context_eq_public_context
    (Γ : VCtx P L) :
    sampleVCtx Γ = pubVCtx Γ := rfl

/-- Commit-guard evaluation is invariant under equality of the acting
player's typed source view. Core commit guards are expressions over
`viewVCtx who Γ`, so they cannot mention fields outside that view. -/
theorem commitGuard_eval_eq_of_viewEnv_eq
    [DecidableEq P]
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {guard :
      L.Expr ((x, b) :: eraseVCtx (viewVCtx who Γ)) L.bool}
    {action : L.Val b}
    {left right : VEnv L Γ}
    (hview : VEnv.toView who left = VEnv.toView who right) :
    evalGuard (Player := P) (L := L) guard action
        (VEnv.eraseEnv (VEnv.toView who left)) =
      evalGuard (Player := P) (L := L) guard action
        (VEnv.eraseEnv (VEnv.toView who right)) := by
  rw [hview]

/-- Pointwise version of `commitGuard_eval_eq_of_viewEnv_eq`: changing values
outside the acting player's visible source context cannot change a commit
guard. -/
theorem commitGuard_eval_eq_of_visible_values_eq
    [DecidableEq P]
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {guard :
      L.Expr ((x, b) :: eraseVCtx (viewVCtx who Γ)) L.bool}
    {action : L.Val b}
    {left right : VEnv L Γ}
    (hvisible :
      ∀ {name bindTy} (hvar : VHasVar (viewVCtx who Γ) name bindTy),
        left name bindTy hvar.ofViewVCtx =
          right name bindTy hvar.ofViewVCtx) :
    evalGuard (Player := P) (L := L) guard action
        (VEnv.eraseEnv (VEnv.toView who left)) =
      evalGuard (Player := P) (L := L) guard action
        (VEnv.eraseEnv (VEnv.toView who right)) := by
  apply commitGuard_eval_eq_of_viewEnv_eq
  funext name bindTy hvar
  exact hvisible hvar

private theorem erasePubVCtx_map_fst_subset_publicVars
    {Γ : VCtx P L} :
    ∀ x, x ∈ (erasePubVCtx Γ).map Prod.fst →
      x ∈ publicVars (L := L) Γ := by
  induction Γ with
  | nil =>
      intro x hx
      simp [erasePubVCtx] at hx
  | cons head tail ih =>
      intro x hx
      obtain ⟨name, binding⟩ := head
      rcases binding with ⟨ty, visibility⟩
      cases visibility with
      | pub =>
          simp only [erasePubVCtx_cons_pub, List.map_cons, List.mem_cons]
            at hx
          rcases hx with rfl | htail
          · simp [publicVars]
          · exact Finset.mem_insert_of_mem (ih x htail)
      | sealed owner =>
          simp only [erasePubVCtx_cons_sealed] at hx
          exact ih x hx

/-- Payoff expressions mention only public source variables. This is the
source-level noninterference boundary for terminal utility: sealed values can
contribute to payoffs only by first being revealed into the public context. -/
theorem payoff_expr_no_sealed_dependency
    {Γ : VCtx P L}
    (payoffs : List (P × L.Expr (erasePubVCtx Γ) L.int)) :
    ∀ entry ∈ payoffs,
      L.exprDeps entry.2 ⊆ publicVars (L := L) Γ := by
  intro entry _hentry name hdep
  exact erasePubVCtx_map_fst_subset_publicVars (L := L)
    name (L.expr_deps_context entry.2 name hdep)

namespace EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-! ## Information-flow validity -/

/-- In a well-formed event graph, public sample nodes read only public fields. -/
theorem sample_reads_public_of_wf
    {G : Graph Player L} (hwf : G.WF)
    {node : Nat} {event : EventNode Player L}
    {dist : EventDist L}
    (hnode : G.nodes[node]? = some event)
    (hsem : event.sem = .sample dist)
    {ref : FieldRef L} (href : ref ∈ dist.reads) :
    G.fieldRefPublic ref := by
  have hnodeWF := hwf node event hnode
  unfold Graph.nodeWFAt at hnodeWF
  rw [hsem] at hnodeWF
  exact hnodeWF.2.2.2 ref href

/-- In a well-formed event graph, commit choice footprints contain only fields
visible to the committing player. -/
theorem commit_choice_reads_visible_of_wf
    {G : Graph Player L} (hwf : G.WF)
    {node : Nat} {event : EventNode Player L}
    {who : Player} {guard : EventGuard L}
    (hnode : G.nodes[node]? = some event)
    (hsem : event.sem = .commit who guard)
    {ref : FieldRef L} (href : ref ∈ guard.choiceReads) :
    G.fieldRefVisibleTo who ref := by
  have hnodeWF := hwf node event hnode
  unfold Graph.nodeWFAt at hnodeWF
  rw [hsem] at hnodeWF
  exact hnodeWF.2.2.2 ref href

/-- In a well-formed event graph, reveal nodes declassify sealed event data
into a public event field of the same type. -/
theorem reveal_opens_sealed_source_of_wf
    {G : Graph Player L} (hwf : G.WF)
    {node : Nat} {event : EventNode Player L}
    {source : Nat}
    (hnode : G.nodes[node]? = some event)
    (hsem : event.sem = .reveal source) :
    ∃ sourceSpec, G.field? source = some sourceSpec ∧
      sourceSpec.ty = event.ty ∧ sourceSpec.owner.isSome ∧
      event.owner = none := by
  have hnodeWF := hwf node event hnode
  unfold Graph.nodeWFAt at hnodeWF
  rw [hsem] at hnodeWF
  exact hnodeWF.2

/-- Paper-facing name for the EventGraph reveal invariant: a reveal opens a
sealed source field into a public event output of the same type. -/
theorem eventGraph_reveal_is_declassification
    {G : Graph Player L} (hwf : G.WF)
    {node : Nat} {event : EventNode Player L}
    {source : Nat}
    (hnode : G.nodes[node]? = some event)
    (hsem : event.sem = .reveal source) :
    ∃ sourceSpec, G.field? source = some sourceSpec ∧
      sourceSpec.ty = event.ty ∧ sourceSpec.owner.isSome ∧
      event.owner = none :=
  reveal_opens_sealed_source_of_wf hwf hnode hsem

/-- Executing a reveal copies the source value into the reveal node's public
output field. Together with `publicObserve`, this is the dynamic
declassification step. -/
theorem reveal_completion_copies_source_to_public_output
    {G : Graph Player L} (hwf : G.WF) {cfg : Config G}
    {node : Fin G.nodeCount} {row : EventNode Player L}
    {source : Nat} {value : L.Val row.ty}
    (hnode : G.nodes[node]? = some row)
    (hsem : row.sem = .reveal source)
    (hvalue : Store.getAs cfg.store source row.ty = some value) :
    row.owner = none ∧
      Store.getAs
          (cfg.completeNode node { ty := row.ty, value := value }).store
          (G.nodeTarget node) row.ty =
        Store.getAs cfg.store source row.ty := by
  rcases reveal_opens_sealed_source_of_wf hwf hnode hsem with
    ⟨_sourceSpec, _hsource, _hty, _hsealed, hpublic⟩
  constructor
  · exact hpublic
  · rw [hvalue]
    simp [Config.completeNode, Store.getAs, Store.set, TypedValue.as?]

/-- In a well-formed event graph, every declared read of a node is available
before that node can run. -/
theorem node_reads_available_before_of_wf
    {G : Graph Player L} (hwf : G.WF)
    {node : Nat} {event : EventNode Player L}
    (hnode : G.nodes[node]? = some event)
    {field : Nat} (hfield : field ∈ event.sem.reads) :
    G.fieldAvailableBefore node field = true := by
  have hnodeWF := hwf node event hnode
  exact hnodeWF.1 field hfield

/-- A reveal node is not ready while an earlier commit node remains undone.
This is the explicit commit/reveal barrier; it is not produced by generic
ambient reads. -/
theorem reveal_not_frontier_with_prior_commit
    {G : Graph Player L} {cfg : Config G}
    {reveal prior : Fin G.nodeCount}
    {revealEvent priorEvent : EventNode Player L}
    (hrevealNode : G.nodes[reveal]? = some revealEvent)
    (hpriorNode : G.nodes[prior]? = some priorEvent)
    (hpriorLt : (prior : Nat) < (reveal : Nat))
    (hreveal : NodeSem.isReveal revealEvent.sem = true)
    (hcommit : NodeSem.isCommit priorEvent.sem = true)
    (hpriorOpen : prior ∉ cfg.done) :
    ¬ Ready G cfg reveal := by
  intro hready
  exact hpriorOpen
    (hready.2
      (G.prior_commit_mem_prereqs_of_reveal
        hrevealNode hpriorNode hpriorLt hreveal hcommit))

/-- A player's observation exposes exactly that player's ready commit nodes. -/
theorem observation_ready_frontier
    (G : Graph Player L) (cfg : Config G) (who : Player) :
    (observe G cfg who).ready = readyCommitNodes G cfg who :=
  observe_ready_eq_readyCommitNodes G cfg who

/-- Equal player observations determine the same ready commit frontier. -/
theorem ready_frontier_eq_of_observation_eq
    {G : Graph Player L} {left right : Config G} {who : Player}
    (hobs : observe G left who = observe G right who) :
    readyCommitNodes G left who = readyCommitNodes G right who :=
  readyCommitNodes_eq_of_observe_eq hobs

/-- Equal public observations determine the same internal frontier. -/
theorem internal_frontier_eq_of_publicObservation_eq
    {G : Graph Player L} {left right : Config G}
    (hobs : publicObserve G left = publicObserve G right) :
    readyInternalNodes G left = readyInternalNodes G right :=
  readyInternalNodes_eq_of_publicObserve_eq hobs

/-- The domain of a locally available frontier action is exactly the ready
frontier in the player's observation. -/
theorem available_action_domain_eq_observed_ready
    {G : Graph Player L} {cfg : Config G} {who : Player}
    {action : FrontierAction G who}
    (havailable : FrontierAction.Available G cfg who action)
    {node : Fin G.nodeCount} :
    (∃ value, action.value? node = some value) ↔
      node ∈ (observe G cfg who).ready :=
  havailable.value?_isSome_iff_observe_ready

/-- Equal player observations determine the same local frontier-action menu. -/
theorem available_action_iff_of_observation_eq
    {G : Graph Player L} {left right : Config G} {who : Player}
    {action : FrontierAction G who}
    (hwf : G.WF)
    (hobs : observe G left who = observe G right who) :
    FrontierAction.Available G left who action ↔
      FrontierAction.Available G right who action :=
  FrontierAction.available_iff_of_observe_eq hwf hobs

/-- A ready commit observation exposes a declared choice read as the current
store value. This is the precise EventGraph replacement for "the acting player
sees what the ready choice is allowed to condition on." -/
theorem ready_commit_observation_choice_reads_store
    {G : Graph Player L} {cfg : Config G} {who : Player}
    {node : Fin G.nodeCount} {row : EventNode Player L}
    {guard : EventGuard L} {field : Fin G.fieldCount}
    (hnode : G.nodes[node]? = some row)
    (hsem : row.sem = .commit who guard)
    (hready : Ready G cfg node)
    (hread :
      ({ field := (field : Nat), ty := (G.fieldRow field).ty } :
        FieldRef L) ∈ guard.choiceReads) :
    (observe G cfg who).fieldValue? node field =
      Store.getAs cfg.store field (G.fieldRow field).ty := by
  have hrowEq : G.nodeRow node = row := by
    have hrow := G.nodes_get?_nodeRow node
    change G.nodes[(node : Nat)]? = some row at hnode
    rw [hnode] at hrow
    exact (Option.some.inj hrow).symm
  have hsem' : (G.nodeRow node).sem = .commit who guard := by
    rw [hrowEq, hsem]
  simp [observe, hsem', hready, hread]

/-- Changing the payload written by a sealed commit node does not change the
public observation. The completed event is public; the sealed payload is not. -/
theorem sealed_commit_payload_no_public_signal
    {G : Graph Player L} (hwf : G.WF) {cfg : Config G}
    {node : Fin G.nodeCount} {row : EventNode Player L}
    {owner : Player} {guard : EventGuard L}
    (hnode : G.nodes[node]? = some row)
    (hsem : row.sem = .commit owner guard)
    (left right : L.Val row.ty) :
    publicObserve G
        (cfg.completeNode node { ty := row.ty, value := left }) =
      publicObserve G
        (cfg.completeNode node { ty := row.ty, value := right }) := by
  have howner : row.owner = some owner := by
    have hnodeWF := hwf node row hnode
    unfold Graph.nodeWFAt at hnodeWF
    rw [hsem] at hnodeWF
    exact hnodeWF.2.2.1
  apply PublicObservation.ext
  · simp [publicObserve, Config.completeNode]
  · intro field
    by_cases hpublic : (G.fieldRow field).owner = none
    · have htargetNe : (field : Nat) ≠ G.nodeTarget node := by
        intro hfield
        have hfieldRow := G.field?_fieldRow field
        have htarget := G.field?_nodeTarget hnode
        rw [hfield] at hfieldRow
        rw [htarget] at hfieldRow
        have hrowSpec := Option.some.inj hfieldRow
        have hownerEq :=
          congrArg (fun spec : FieldSpec Player L => spec.owner) hrowSpec
        rw [howner] at hownerEq
        change some owner = (G.fieldRow field).owner at hownerEq
        rw [hpublic] at hownerEq
        cases hownerEq
      have hleftStore :
          Store.getAs
              (Store.set cfg.store (G.nodeTarget node)
                { ty := row.ty, value := left })
              field (G.fieldRow field).ty =
            Store.getAs cfg.store field (G.fieldRow field).ty :=
        Store.getAs_set_ne cfg.store htargetNe
          { ty := row.ty, value := left } (G.fieldRow field).ty
      have hrightStore :
          Store.getAs
              (Store.set cfg.store (G.nodeTarget node)
                { ty := row.ty, value := right })
              field (G.fieldRow field).ty =
            Store.getAs cfg.store field (G.fieldRow field).ty :=
        Store.getAs_set_ne cfg.store htargetNe
          { ty := row.ty, value := right } (G.fieldRow field).ty
      simp [publicObserve, hpublic, Config.completeNode,
        Config.nodeDone, Config.doneIds, hleftStore, hrightStore]
    · simp [publicObserve, hpublic]

/-- Changing the payload written by a sealed commit node does not change a
different player's graph observation. Non-owners may see that the commit
completed, but a well-formed graph never exposes the sealed target field in a
non-owner ready commit view. -/
theorem sealed_commit_payload_no_observe_signal_to_nonowner
    {G : Graph Player L} (hwf : G.WF) {cfg : Config G}
    {node : Fin G.nodeCount} {row : EventNode Player L}
    {owner observer : Player} {guard : EventGuard L}
    (hnode : G.nodes[node]? = some row)
    (hsem : row.sem = .commit owner guard)
    (hne : observer ≠ owner)
    (left right : L.Val row.ty) :
    observe G
        (cfg.completeNode node { ty := row.ty, value := left })
        observer =
      observe G
        (cfg.completeNode node { ty := row.ty, value := right })
        observer := by
  have howner : row.owner = some owner := by
    have hnodeWF := hwf node row hnode
    unfold Graph.nodeWFAt at hnodeWF
    rw [hsem] at hnodeWF
    exact hnodeWF.2.2.1
  apply Observation.ext
  · ext query
    simp [observe, Config.completeNode, Ready]
  · intro query field
    by_cases htarget : (field : Nat) = G.nodeTarget node
    · have hnotRead :
          ∀ queryRow queryGuard,
            G.nodes[query]? = some queryRow →
            queryRow.sem = .commit observer queryGuard →
            ({ field := (field : Nat), ty := (G.fieldRow field).ty } :
              FieldRef L) ∉ queryGuard.choiceReads := by
        intro queryRow queryGuard hquery hquerySem hread
        have hvis :=
          commit_choice_reads_visible_of_wf
            (G := G) hwf hquery hquerySem hread
        rcases hvis with ⟨spec, hspec, _hty, hspecOwner⟩
        have htargetSpec := G.field?_nodeTarget hnode
        rw [htarget] at hspec
        rw [htargetSpec] at hspec
        have hspecEq := Option.some.inj hspec
        have hownerEq :=
          congrArg (fun spec : FieldSpec Player L => spec.owner) hspecEq
        rw [howner] at hownerEq
        have hownerEq' : some owner = spec.owner := by
          simpa using hownerEq
        rcases hspecOwner with hpublic | hobserver
        · rw [← hownerEq'] at hpublic
          cases hpublic
        · rw [← hownerEq'] at hobserver
          exact hne (Option.some.inj hobserver).symm
      cases hquerySem : (G.nodeRow query).sem with
      | sample dist =>
          simp [observe, hquerySem]
      | reveal source =>
          simp [observe, hquerySem]
      | commit actor queryGuard =>
          by_cases hactor : actor = observer
          · subst actor
            have hqueryRow := G.nodes_get?_nodeRow query
            have hnotReadRow :
                ({ field := (field : Nat),
                    ty := (G.fieldRow field).ty } : FieldRef L) ∉
                  queryGuard.choiceReads :=
              hnotRead (G.nodeRow query) queryGuard hqueryRow hquerySem
            simp [observe, hquerySem, Config.completeNode, Ready,
              hnotReadRow]
          · simp [observe, hquerySem, hactor]
    · have hleftStore :
          Store.getAs
              (Store.set cfg.store (G.nodeTarget node)
                { ty := row.ty, value := left })
              field (G.fieldRow field).ty =
            Store.getAs cfg.store field (G.fieldRow field).ty :=
        Store.getAs_set_ne cfg.store htarget
          { ty := row.ty, value := left } (G.fieldRow field).ty
      have hrightStore :
          Store.getAs
              (Store.set cfg.store (G.nodeTarget node)
                { ty := row.ty, value := right })
              field (G.fieldRow field).ty =
            Store.getAs cfg.store field (G.fieldRow field).ty :=
        Store.getAs_set_ne cfg.store htarget
          { ty := row.ty, value := right } (G.fieldRow field).ty
      simp [observe, Config.completeNode, Ready, hleftStore, hrightStore]

/-- On reachable checkpoint states, equal player observations determine the
same local frontier-action menu. -/
theorem frontier_available_actions_eq_of_observation_eq
    {G : Graph Player L}
    {left right : ReachableConfig G} {who : Player}
    (hwf : G.WF)
    (hobs : observe G left.1 who = observe G right.1 who) :
    frontierAvailableActions G left who =
      frontierAvailableActions G right who :=
  frontierAvailableActions_eq_of_observe_eq hwf hobs

/-- A sealed commit payload cannot signal to a non-owner through the graph
observation surface. The non-owner may observe completion, but not the chosen
sealed value. -/
theorem commit_payload_no_signal_to_nonowner
    {G : Graph Player L} {cfg : Config G}
    {node : Fin G.nodeCount} {row : EventNode Player L}
    {owner observer : Player} {guard : EventGuard L}
    (hwf : G.WF)
    (hnode : G.nodes[node]? = some row)
    (hsem : row.sem = .commit owner guard)
    (hne : observer ≠ owner)
    (left right : L.Val row.ty) :
    observe G
        (cfg.completeNode node { ty := row.ty, value := left })
        observer =
      observe G
        (cfg.completeNode node { ty := row.ty, value := right })
        observer :=
  sealed_commit_payload_no_observe_signal_to_nonowner
    hwf hnode hsem hne left right

/-- Observation-equivalent states have the same local strategic menu. This is
the EventGraph-level non-signalling statement for unrevealed sealed values:
unrevealed storage matters strategically only if it changes the observer's
defined graph observation. -/
theorem unrevealed_sealed_values_no_signal
    {G : Graph Player L}
    {left right : ReachableConfig G} {who : Player}
    (hwf : G.WF)
    (hobs : observe G left.1 who = observe G right.1 who) :
    frontierAvailableActions G left who =
      frontierAvailableActions G right who :=
  frontier_available_actions_eq_of_observation_eq hwf hobs

/-- A player's activity at a frontier checkpoint is determined by the public
checkpoint observation together with that player's private graph observation. -/
theorem frontier_activity_iff_of_observations_eq
    [Fintype Player]
    {G : Graph Player L}
    {left right : ReachableConfig G} {who : Player}
    (hpublic : publicObserve G left.1 = publicObserve G right.1)
    (hprivate : observe G left.1 who = observe G right.1 who) :
    who ∈ frontierActive G left ↔ who ∈ frontierActive G right :=
  mem_frontierActive_iff_of_observe_eq hpublic hprivate

/-! ## Schedule-local observational invariance -/

/-- Swapping two distinct available primitive events preserves the checkpoint
public observation and every player's graph observation. -/
theorem two_event_swap_preserves_observations
    {G : Graph Player L} (hwf : G.WF)
    {src : ReachableConfig G}
    (left right : AvailableEvent G src.1)
    (hne : left.node ≠ right.node)
    {leftNext rightNext : Config G}
    (hleft :
      leftNext ∈ (stepAvailableEvent G src.1 left).support)
    (hright :
      rightNext ∈ (stepAvailableEvent G src.1 right).support) :
    ∃ leftFinal rightFinal : ReachableConfig G,
      Nonempty (BatchStep G src leftFinal) ∧
      Nonempty (BatchStep G src rightFinal) ∧
      publicObserve G leftFinal.1 = publicObserve G rightFinal.1 ∧
      ∀ who : Player,
        observe G leftFinal.1 who = observe G rightFinal.1 who :=
  BatchStep.two_event_swap_observations
    hwf left right hne hleft hright

/-- A local adjacent swap remains observationally valid after replaying the
same subsequent primitive batch tail. -/
theorem two_event_swap_with_tail_preserves_observations
    {G : Graph Player L} (hwf : G.WF)
    {src : ReachableConfig G}
    (left right : AvailableEvent G src.1)
    (hne : left.node ≠ right.node)
    {leftNext rightNext : Config G}
    (hleft :
      leftNext ∈ (stepAvailableEvent G src.1 left).support)
    (hright :
      rightNext ∈ (stepAvailableEvent G src.1 right).support) :
    ∃ leftFinal rightFinal : ReachableConfig G,
      Nonempty (BatchStep G src leftFinal) ∧
      Nonempty (BatchStep G src rightFinal) ∧
      leftFinal.1 = rightFinal.1 ∧
      ∀ {dst : ReachableConfig G}, BatchStep G leftFinal dst →
        ∃ dst' : ReachableConfig G,
          Nonempty (BatchStep G src dst) ∧
          Nonempty (BatchStep G src dst') ∧
          publicObserve G dst'.1 = publicObserve G dst.1 ∧
          (∀ who : Player,
            observe G dst'.1 who = observe G dst.1 who) :=
  BatchStep.two_event_swap_with_tail_observations
    hwf left right hne hleft hright

/-- Adjacent-swap schedule invariance can be applied after an already-executed
batch prefix. -/
theorem two_event_swap_after_prefix_preserves_observations
    {G : Graph Player L} (hwf : G.WF)
    {src mid : ReachableConfig G}
    (pref : Nonempty (BatchStep G src mid))
    (left right : AvailableEvent G mid.1)
    (hne : left.node ≠ right.node)
    {leftNext rightNext : Config G}
    (hleft :
      leftNext ∈ (stepAvailableEvent G mid.1 left).support)
    (hright :
      rightNext ∈ (stepAvailableEvent G mid.1 right).support) :
    ∃ leftFinal rightFinal : ReachableConfig G,
      Nonempty (BatchStep G mid leftFinal) ∧
      Nonempty (BatchStep G mid rightFinal) ∧
      leftFinal.1 = rightFinal.1 ∧
      ∀ {dst : ReachableConfig G}, BatchStep G leftFinal dst →
        ∃ dst' : ReachableConfig G,
          Nonempty (BatchStep G src dst) ∧
          Nonempty (BatchStep G src dst') ∧
          publicObserve G dst'.1 = publicObserve G dst.1 ∧
          (∀ who : Player,
            observe G dst'.1 who = observe G dst.1 who) :=
  BatchStep.two_event_swap_after_prefix_with_tail_observations
    hwf pref left right hne hleft hright

end EventGraph

namespace WFProgram

variable {P : Type} [DecidableEq P] {L : IExpr}

/-! ## Compiled-program visibility -/

/-- Compiled payoff projections read only public fields that are available at
terminal graph states. Hidden values affect payoffs only after reveal has
produced public graph data. -/
theorem compiled_payoff_reads_public_terminal_available
    (program : WFProgram P L)
    {payoff : P × EventGraph.EventPayoff L}
    (hpayoff : payoff ∈ (ToEventGraph.compile program.core).payoffs)
    {ref : EventGraph.FieldRef L} (href : ref ∈ payoff.2.reads) :
    (ToEventGraph.compile program.core).graph.fieldRefPublic ref ∧
      (ToEventGraph.compile program.core).graph.fieldAvailableBefore
        (ToEventGraph.compile program.core).graph.nodeCount ref.field =
        true :=
  program.compiledPayoffs_wf payoff hpayoff ref href

/-- Compiled graph sample nodes read only public graph fields. -/
theorem compiled_sample_reads_public
    (program : WFProgram P L)
    {node : Nat} {event : EventGraph.EventNode P L}
    {dist : EventGraph.EventDist L}
    (hnode :
      (ToEventGraph.compile program.core).graph.nodes[node]? = some event)
    (hsem : event.sem = .sample dist)
    {ref : EventGraph.FieldRef L} (href : ref ∈ dist.reads) :
    (ToEventGraph.compile program.core).graph.fieldRefPublic ref :=
  EventGraph.sample_reads_public_of_wf
    program.compiledGraph_wf hnode hsem href

/-- Compiled graph commit choice footprints contain only information visible
to the acting player. -/
theorem compiled_commit_choice_reads_visible
    (program : WFProgram P L)
    {node : Nat} {event : EventGraph.EventNode P L}
    {who : P} {guard : EventGraph.EventGuard L}
    (hnode :
      (ToEventGraph.compile program.core).graph.nodes[node]? = some event)
    (hsem : event.sem = .commit who guard)
    {ref : EventGraph.FieldRef L} (href : ref ∈ guard.choiceReads) :
    (ToEventGraph.compile program.core).graph.fieldRefVisibleTo who ref :=
  EventGraph.commit_choice_reads_visible_of_wf
    program.compiledGraph_wf hnode hsem href

/-- Compiled graph reveal nodes are the only public declassification nodes:
their source field is sealed and their output field is public. -/
theorem compiled_reveal_opens_sealed_source
    (program : WFProgram P L)
    {node : Nat} {event : EventGraph.EventNode P L}
    {source : Nat}
    (hnode :
      (ToEventGraph.compile program.core).graph.nodes[node]? = some event)
    (hsem : event.sem = .reveal source) :
    ∃ sourceSpec,
      (ToEventGraph.compile program.core).graph.field? source =
        some sourceSpec ∧
      sourceSpec.ty = event.ty ∧ sourceSpec.owner.isSome ∧
      event.owner = none :=
  EventGraph.reveal_opens_sealed_source_of_wf
    program.compiledGraph_wf hnode hsem

end WFProgram

end Vegas
