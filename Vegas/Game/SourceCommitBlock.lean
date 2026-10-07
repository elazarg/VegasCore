/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceStateKernel
import Vegas.Source.ObservationRecall

/-! # A run of leading commitments in the source protocol

A program whose first `count` operations are commitments (`Vegas.CommitPrefix`)
continues, after them, in a residual program (`Vegas.commitTail`). The source
protocol runs the commitments one after another: each owner draws from its
behavioral kernel at its view (`Vegas.kernelChain`).

When one player's choices are supplied instead, as a list in order
(`Vegas.listChain`), and those choices come with further data whose law
depends on the state only through that player's information, the run is again
the source run in which that player follows behavioral kernels, and the further
data factors through the player's new view
(`Vegas.listChain_factorization`). Every other owner's choice is independent
of that player's information beyond its own view, because commitments are
hidden from everyone but their owner.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- The first `count` operations of the program are commitments. -/
def CommitPrefix : {Γ : SourceCtx Player L} → {names : Finset VarId} →
    SourceProgram Player L Γ names → Nat → Prop
  | _, _, _, 0 => True
  | _, _, .commit _ _ _ _ next, count + 1 => CommitPrefix next count
  | _, _, .ret _, _ + 1 => False
  | _, _, .sample _ _ _ _, _ + 1 => False
  | _, _, .reveal _ _ _ _ _ _ _, _ + 1 => False

/-- The residual program after some leading operations, and the embedding of
its protocol states. -/
structure ResidualProgram {Γ : SourceCtx Player L} {names : Finset VarId}
    (program : SourceProgram Player L Γ names) where
  context : SourceCtx Player L
  names : Finset VarId
  tail : SourceProgram Player L context names
  lift : ProtocolState tail → ProtocolState program

/-- The residual program after `count` leading commitments. -/
def commitTail : (count : Nat) → {Γ : SourceCtx Player L} → {names : Finset VarId} →
    (program : SourceProgram Player L Γ names) → CommitPrefix program count →
      ResidualProgram program
  | 0, _, _, program, _ => ⟨_, _, program, id⟩
  | count + 1, _, _, .commit _ _ _ _ next, prefixed =>
      let rest := commitTail count next prefixed
      ⟨rest.context, rest.names, rest.tail, Sum.inr ∘ rest.lift⟩
  | _ + 1, _, _, .ret _, prefixed => prefixed.elim
  | _ + 1, _, _, .sample _ _ _ _, prefixed => prefixed.elim
  | _ + 1, _, _, .reveal _ _ _ _ _ _ _, prefixed => prefixed.elim

/-- The residual profile after `count` leading commitments. -/
def commitTailProfile : (count : Nat) → {Γ : SourceCtx Player L} → {names : Finset VarId} →
    (program : SourceProgram Player L Γ names) → (prefixed : CommitPrefix program count) →
    BehavioralProfile program → BehavioralProfile (commitTail count program prefixed).tail
  | 0, _, _, _, _, profile => profile
  | count + 1, _, _, .commit _ _ _ _ next, prefixed, profile =>
      commitTailProfile count next prefixed (afterCommit profile)
  | _ + 1, _, _, .ret _, prefixed, _ => prefixed.elim
  | _ + 1, _, _, .sample _ _ _ _, prefixed, _ => prefixed.elim
  | _ + 1, _, _, .reveal _ _ _ _ _ _ _, prefixed, _ => prefixed.elim

/-- A policy whose decisions at the leading commitments are those of `head`
and whose residual policy is `rest`. -/
def graftPolicy (who : Player) : (count : Nat) → {Γ : SourceCtx Player L} →
    {names : Finset VarId} → (program : SourceProgram Player L Γ names) →
    (prefixed : CommitPrefix program count) → BehavioralPolicy who program →
    BehavioralPolicy who (commitTail count program prefixed).tail → BehavioralPolicy who program
  | 0, _, _, _, _, _, rest => rest
  | count + 1, _, _, .commit _ _ _ _ next, prefixed, head, rest =>
      (head.1, graftPolicy who count next prefixed head.2 rest)
  | _ + 1, _, _, .ret _, prefixed, _, _ => prefixed.elim
  | _ + 1, _, _, .sample _ _ _ _, prefixed, _, _ => prefixed.elim
  | _ + 1, _, _, .reveal _ _ _ _ _ _ _, prefixed, _, _ => prefixed.elim

/-- The source law of the configuration after `count` leading commitments,
every owner drawing from its kernel, `who` following `policy`. -/
def kernelChain (who : Player) : (count : Nat) → {Γ : SourceCtx Player L} →
    {names : Finset VarId} → (program : SourceProgram Player L Γ names) →
    BehavioralProfile program → BehavioralPolicy who program →
    (prefixed : CommitPrefix program count) → Config Player L Γ →
      PMF (Config Player L (commitTail count program prefixed).context)
  | 0, _, _, _, _, _, _, config => PMF.pure config
  | count + 1, _, _, .commit name _ _ guard next, profile, policy, prefixed, config =>
      (commitKernel (Function.update profile who policy) (config.view _)).bind fun choice =>
        kernelChain who count next (afterCommit profile) policy.2 prefixed
          (commitSuccessor name guard config choice)
  | _ + 1, _, _, .ret _, _, _, prefixed, _ => prefixed.elim
  | _ + 1, _, _, .sample _ _ _ _, _, _, prefixed, _ => prefixed.elim
  | _ + 1, _, _, .reveal _ _ _ _ _ _ _, _, _, prefixed, _ => prefixed.elim

/-- The source law of the configuration after `count` leading commitments,
every owner satisfying `drawn` drawing from its kernel and every other owner
taking its successive choices from a list; a missing or mismatched entry is a
failed binding. -/
def listChain (drawn : Player → Prop) [DecidablePred drawn] : (count : Nat) →
    {Γ : SourceCtx Player L} →
    {names : Finset VarId} → (program : SourceProgram Player L Γ names) →
    BehavioralProfile program → (prefixed : CommitPrefix program count) →
    Config Player L Γ → List (OwnAction Player L) →
      PMF (Config Player L (commitTail count program prefixed).context)
  | 0, _, _, _, _, _, config, _ => PMF.pure config
  | count + 1, _, _, .commit (payload := payload) name owner _ guard next, profile, prefixed,
      config, choices =>
      if drawn owner then
        (commitKernel profile (config.view owner)).bind fun choice =>
          listChain drawn count next (afterCommit profile) prefixed
            (commitSuccessor name guard config choice) choices
      else
        listChain drawn count next (afterCommit profile) prefixed
          (commitSuccessor name guard config (OwnAction.binding owner name payload choices.head?))
          choices.tail
  | _ + 1, _, _, .ret _, _, prefixed, _, _ => prefixed.elim
  | _ + 1, _, _, .sample _ _ _ _, _, prefixed, _, _ => prefixed.elim
  | _ + 1, _, _, .reveal _ _ _ _ _ _ _, _, prefixed, _, _ => prefixed.elim

omit [IExpr.ResultTypes L] in
/-- The owner's view after its commitment determines its view before and its
choice. -/
private theorem commit_view_reflects {Γ : SourceCtx Player L} {who : Player}
    {payload : L.Ty} (name : VarId) (guard : SourceGuard L Γ who name payload)
    (left right : Config Player L Γ) (first second : PublicationResult (L.Val payload))
    (same : (commitSuccessor name guard left first).view who =
      (commitSuccessor name guard right second).view who) :
    left.view who = right.view who ∧ first = second := by
  constructor
  · calc left.view who = ((commitSuccessor name guard left first).view who).back
            (decide (who = who)) := (back_commit_view who name guard left first).symm
      _ = ((commitSuccessor name guard right second).view who).back (decide (who = who)) :=
          congrArg _ same
      _ = right.view who := back_commit_view who name guard right second
  · have cell := congrArg (fun view : DecisionView who ((name, .commitment who payload) :: Γ) =>
      view.1.cells.get .here) same
    simp only [Config.view, commitSuccessor, sourceObserve, Env.get, Env.cons, ite_true] at cell
    exact Option.some.inj cell

/-- A law of further data that depends on the seed only through a readout
factors through that readout. -/
private theorem exists_outcome_of_read {Seed Read Outcome : Type} (prior : PMF Seed)
    (read : Seed → Read) (outcome : Seed → PMF Outcome)
    (coupled : ∀ left ∈ prior.support, ∀ right ∈ prior.support,
      read left = read right → outcome left = outcome right) :
    ∃ through : Read → PMF Outcome, ∀ seed ∈ prior.support, outcome seed = through (read seed) := by
  classical
  obtain ⟨anchor, anchored⟩ := prior.support_nonempty
  refine ⟨fun value => if found : ∃ seed ∈ prior.support, read seed = value then
    outcome found.choose else outcome anchor, fun seed supported => ?_⟩
  have found : ∃ other ∈ prior.support, read other = read seed := ⟨seed, supported, rfl⟩
  simp only [found, ↓reduceDIte]
  exact (coupled _ found.choose_spec.1 seed supported found.choose_spec.2).symm

/-- **Leading commitments against one player's supplied choices.** Suppose
that, besides the source configuration, each seed carries a readout whose law
given the configuration depends only on `who`'s view, and a law of `who`'s
choices at the leading commitments with further data, which depends on the
seed only through the readout. Then running the commitments with `who`'s
supplied choices and every other owner's kernel is the source run in which
`who` follows behavioral kernels at its commitments, and the further data
factors through `who`'s view after the commitments. -/
theorem listChain_factorization (who : Player) :
    ∀ (count : Nat) {Γ : SourceCtx Player L} {names : Finset VarId}
      (program : SourceProgram Player L Γ names) (profile : BehavioralProfile program)
      (prefixed : CommitPrefix program count)
      {Seed Read Final : Type} (prior : PMF Seed) (source : Seed → Config Player L Γ)
      (read : Seed → Read) (noise : DecisionView who Γ → PMF Read),
      prior.map (fun seed => (source seed, read seed)) =
        (prior.map source).bind (fun config =>
          (noise (config.view who)).map fun extra => (config, extra)) →
      ∀ (outcome : Seed → PMF (List (OwnAction Player L) × Final)),
      (∀ left ∈ prior.support, ∀ right ∈ prior.support,
        read left = read right → outcome left = outcome right) →
      ∃ policy : BehavioralPolicy who program,
        ∃ nextNoise : DecisionView who (commitTail count program prefixed).context → PMF Final,
          (prior.bind fun seed => (outcome seed).bind fun pair =>
            (listChain (· ≠ who) count program profile prefixed (source seed) pair.1).map
              fun config => (config, pair.2)) =
          ((prior.map source).bind (kernelChain who count program profile policy prefixed)).bind
            fun config => (nextNoise (config.view who)).map fun extra => (config, extra) := by
  intro count
  induction count with
  | zero =>
      intro Γ names program profile prefixed Seed Read Final prior source read noise factor
        outcome coupled
      obtain ⟨through, throughEq⟩ := exists_outcome_of_read prior read outcome coupled
      refine ⟨profile who, fun view => (noise view).bind fun extra =>
        (through extra).map Prod.snd, ?_⟩
      have native : (prior.bind fun seed => (outcome seed).bind fun pair =>
          (listChain (· ≠ who) 0 program profile prefixed (source seed) pair.1).map
            fun config => (config, pair.2)) =
          (prior.map fun seed => (source seed, read seed)).bind fun point =>
            (through point.2).map fun pair => (point.1, pair.2) := by
        rw [PMF.bind_map]
        apply bind_congr_on_support _
        intro seed supported
        simp only [Function.comp_apply, throughEq seed supported, listChain, PMF.pure_map]
        rfl
      rw [native, factor, PMF.bind_bind]
      simp only [kernelChain, PMF.bind_pure, PMF.bind_map, PMF.map_bind, Function.comp_def,
        PMF.map_comp]
  | succ count ih =>
      intro Γ names program profile prefixed Seed Read Final prior source read noise factor
        outcome coupled
      cases program with
      | ret _ => exact prefixed.elim
      | sample _ _ _ _ => exact prefixed.elim
      | reveal _ _ _ _ _ _ _ => exact prefixed.elim
      | @commit Γ names name owner payload fresh guard next =>
          by_cases own : owner = who
          · subst owner
            obtain ⟨through, throughEq⟩ := exists_outcome_of_read prior read outcome coupled
            let split := fun pair : List (OwnAction Player L) × Final =>
              (OwnAction.binding who name payload pair.1.head?, (pair.1.tail, pair.2))
            let mixed := fun view : DecisionView who Γ =>
              ((noise view).bind through).map split
            let kernel := fun view : DecisionView who Γ => (mixed view).map Prod.fst
            let rest := fun (view : DecisionView who Γ)
                (choice : PublicationResult (L.Val payload)) =>
              (fiberPosterior (mixed view) Prod.fst choice).map Prod.snd
            let NextSeed := Config Player L Γ × PublicationResult (L.Val payload)
            let nextPrior : PMF NextSeed := (prior.map source).bind fun config =>
              (kernel (config.view who)).map fun choice => (config, choice)
            let nextSource := fun point : NextSeed => commitSuccessor name guard point.1 point.2
            let nextRead := fun point : NextSeed => (nextSource point).view who
            let nextOutcome := fun point : NextSeed => rest (point.1.view who) point.2
            have nextFactor : nextPrior.map (fun point => (nextSource point, nextRead point)) =
                (nextPrior.map nextSource).bind fun config =>
                  (PMF.pure (config.view who)).map fun extra => (config, extra) := by
              rw [PMF.bind_map]
              simp only [Function.comp_def, PMF.pure_map]
              rw [← PMF.bind_pure_comp]
              rfl
            have nextCoupled : ∀ left ∈ nextPrior.support, ∀ right ∈ nextPrior.support,
                nextRead left = nextRead right → nextOutcome left = nextOutcome right := by
              intro left _ right _ same
              obtain ⟨views, choices⟩ := commit_view_reflects name guard left.1 right.1 left.2
                right.2 same
              simp only [nextOutcome, views, choices]
            obtain ⟨tailPolicy, nextNoise, tailLaw⟩ := ih next (afterCommit profile) prefixed
              nextPrior nextSource nextRead (fun view => PMF.pure view) nextFactor nextOutcome
              nextCoupled
            refine ⟨(fun _ view => kernel view, tailPolicy), nextNoise, ?_⟩
            have native : (prior.bind fun seed => (outcome seed).bind fun pair =>
                (listChain (· ≠ who) (count + 1) (.commit name who fresh guard next) profile
                  prefixed (source seed) pair.1).map fun config => (config, pair.2)) =
                nextPrior.bind fun point => (nextOutcome point).bind fun pair =>
                  (listChain (· ≠ who) count next (afterCommit profile) prefixed (nextSource point)
                    pair.1).map fun config => (config, pair.2) := by
              have perSeed : ∀ seed ∈ prior.support,
                  ((outcome seed).bind fun pair =>
                    (listChain (· ≠ who) (count + 1) (.commit name who fresh guard next) profile
                      prefixed (source seed) pair.1).map fun config => (config, pair.2)) =
                  ((through (read seed)).map split).bind fun parts =>
                    (listChain (· ≠ who) count next (afterCommit profile) prefixed
                      (commitSuccessor name guard (source seed) parts.1) parts.2.1).map
                        fun config => (config, parts.2.2) := by
                intro seed supported
                rw [throughEq seed supported, PMF.bind_map]
                apply bind_congr_on_support _
                intro pair _
                simp only [listChain, ne_eq, not_true_eq_false, ↓reduceIte, Function.comp_apply,
                  split]
                rfl
              calc
                _ = (prior.map fun seed => (source seed, read seed)).bind fun point =>
                    ((through point.2).map split).bind fun parts =>
                      (listChain (· ≠ who) count next (afterCommit profile) prefixed
                        (commitSuccessor name guard point.1 parts.1) parts.2.1).map
                          fun config => (config, parts.2.2) := by
                  rw [PMF.bind_map]
                  exact bind_congr_on_support _ perSeed
                _ = (prior.map source).bind fun config => (mixed (config.view who)).bind
                    fun parts => (listChain (· ≠ who) count next (afterCommit profile) prefixed
                      (commitSuccessor name guard config parts.1) parts.2.1).map
                        fun result => (result, parts.2.2) := by
                  rw [factor, PMF.bind_bind]
                  apply bind_congr_on_support _
                  intro config _
                  simp only [mixed, PMF.bind_map, PMF.map_bind, Function.comp_def, PMF.bind_bind]
                _ = (prior.map source).bind fun config =>
                    (kernel (config.view who)).bind fun choice =>
                      (rest (config.view who) choice).bind fun parts =>
                        (listChain (· ≠ who) count next (afterCommit profile) prefixed
                          (commitSuccessor name guard config choice) parts.1).map
                            fun result => (result, parts.2) := by
                  apply bind_congr_on_support _
                  intro config _
                  conv_lhs => rw [eq_bind_fst_fiberPosterior_snd (mixed (config.view who))]
                  simp only [kernel, rest, PMF.bind_bind, PMF.bind_map, Function.comp_def,
                    PMF.map_comp]
                _ = _ := by
                  simp only [nextPrior, PMF.bind_bind, PMF.bind_map, Function.comp_def,
                    nextOutcome, nextSource]
            rw [native, tailLaw]
            simp only [nextPrior, PMF.bind_bind, PMF.bind_map, PMF.map_bind, Function.comp_def,
              kernelChain, nextSource]
            apply bind_congr_on_support _
            intro config _
            simp only [commitKernel, Function.update_self]
            rfl
          · let NextSeed := Seed × PublicationResult (L.Val payload)
            let nextPrior : PMF NextSeed := prior.bind fun seed =>
              (commitKernel profile ((source seed).view owner)).map fun choice => (seed, choice)
            let nextSource := fun point : NextSeed =>
              commitSuccessor name guard (source point.1) point.2
            let nextRead := fun point : NextSeed => read point.1
            let nextNoiseIn :=
                fun view : DecisionView who ((name, .commitment owner payload) :: Γ) =>
              noise (view.back (decide (owner = who)))
            have nextFactor : nextPrior.map (fun point => (nextSource point, nextRead point)) =
                (nextPrior.map nextSource).bind fun config =>
                  (nextNoiseIn (config.view who)).map fun extra => (config, extra) := by
              have joint : nextPrior.map (fun point => (nextSource point, nextRead point)) =
                  (prior.map fun seed => (source seed, read seed)).bind fun point =>
                    (commitKernel profile (point.1.view owner)).map fun choice =>
                      (commitSuccessor name guard point.1 choice, point.2) := by
                simp only [nextPrior, PMF.map_bind, PMF.bind_map, PMF.map_comp,
                  Function.comp_def]
                rfl
              rw [joint, factor, PMF.bind_bind]
              simp only [nextPrior, PMF.map_bind, PMF.bind_map, PMF.bind_bind, PMF.map_comp,
                Function.comp_def, nextNoiseIn, nextSource, back_commit_view]
              apply bind_congr_on_support _
              intro config _
              simp only [← PMF.bind_pure_comp, Function.comp_def]
              exact PMF.bind_comm _ _ _
            have nextCoupled : ∀ left ∈ nextPrior.support, ∀ right ∈ nextPrior.support,
                nextRead left = nextRead right → outcome left.1 = outcome right.1 := by
              intro left leftSupport right rightSupport same
              have leftSeed : left.1 ∈ prior.support := by
                rw [PMF.mem_support_bind_iff] at leftSupport
                obtain ⟨seed, seedSupport, member⟩ := leftSupport
                obtain ⟨choice, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
                exact seedSupport
              have rightSeed : right.1 ∈ prior.support := by
                rw [PMF.mem_support_bind_iff] at rightSupport
                obtain ⟨seed, seedSupport, member⟩ := rightSupport
                obtain ⟨choice, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
                exact seedSupport
              exact coupled _ leftSeed _ rightSeed same
            obtain ⟨tailPolicy, nextNoise, tailLaw⟩ := ih next (afterCommit profile) prefixed
              nextPrior nextSource nextRead nextNoiseIn nextFactor (fun point => outcome point.1)
              nextCoupled
            refine ⟨(fun same _ => absurd same own, tailPolicy), nextNoise, ?_⟩
            have native : (prior.bind fun seed => (outcome seed).bind fun pair =>
                (listChain (· ≠ who) (count + 1) (.commit name owner fresh guard next) profile
                  prefixed (source seed) pair.1).map fun config => (config, pair.2)) =
                nextPrior.bind fun point => (outcome point.1).bind fun pair =>
                  (listChain (· ≠ who) count next (afterCommit profile) prefixed (nextSource point)
                    pair.1).map fun config => (config, pair.2) := by
              simp only [nextPrior, PMF.bind_bind, PMF.bind_map, Function.comp_def, nextSource]
              apply bind_congr_on_support _
              intro seed _
              simp only [listChain, ne_eq, own, not_false_eq_true, ↓reduceIte, PMF.map_bind]
              rw [PMF.bind_comm]
              rfl
            rw [native, tailLaw]
            simp only [nextPrior, PMF.bind_bind, PMF.bind_map, PMF.map_bind, Function.comp_def,
              kernelChain, nextSource]
            apply bind_congr_on_support _
            intro seed _
            simp only [commitKernel, Function.update_of_ne own]
            rfl

/-- With every owner drawing from its kernel, the chain is the kernel chain of
the profile itself. -/
theorem listChain_all (who : Player) :
    ∀ (count : Nat) {Γ : SourceCtx Player L} {names : Finset VarId}
      (program : SourceProgram Player L Γ names) (profile : BehavioralProfile program)
      (prefixed : CommitPrefix program count) (config : Config Player L Γ)
      (choices : List (OwnAction Player L)),
      listChain (fun _ => True) count program profile prefixed config choices =
        kernelChain who count program profile (profile who) prefixed config := by
  intro count
  induction count with
  | zero => intro Γ names program profile prefixed config choices; rfl
  | succ count ih =>
      intro Γ names program profile prefixed config choices
      cases program with
      | ret _ => exact prefixed.elim
      | sample _ _ _ _ => exact prefixed.elim
      | reveal _ _ _ _ _ _ _ => exact prefixed.elim
      | commit name owner fresh guard next =>
          simp only [listChain, ↓reduceIte, kernelChain, Function.update_eq_self]
          apply bind_congr_on_support _
          intro choice _
          exact ih next (afterCommit profile) prefixed _ choices

/-- The commitment kernels depend only on the deciding player's kernel at the
first commitment. -/
private theorem commitKernel_update_head {Γ : SourceCtx Player L} {names : Finset VarId}
    {name : VarId} {owner : Player} {payload : L.Ty} {fresh : name ∉ Γ.map Prod.fst}
    {guard : SourceGuard L Γ owner name payload}
    {next : SourceProgram Player L ((name, .commitment owner payload) :: Γ) (insert name names)}
    (profile : BehavioralProfile (.commit name owner fresh guard next)) (who : Player)
    (first second : BehavioralPolicy who (.commit name owner fresh guard next))
    (same : first.1 = second.1) :
    commitKernel (Function.update profile who first) =
      commitKernel (Function.update profile who second) := by
  by_cases own : owner = who
  · subst owner
    simp only [commitKernel, Function.update_self, same]
  · simp only [commitKernel, Function.update_of_ne own]

/-- **The source run through grafted leading commitments.** With a policy
whose leading commitment kernels are those of `head` and whose residual policy
is `rest`, the source run is the kernel chain through the commitments followed
by the residual source run. -/
theorem iterate_graftPolicy [Fintype Player] (who : Player) :
    ∀ (count : Nat) {Γ : SourceCtx Player L} {names : Finset VarId}
      (program : SourceProgram Player L Γ names) (profile : BehavioralProfile program)
      (prefixed : CommitPrefix program count) (head : BehavioralPolicy who program)
      (rest : BehavioralPolicy who (commitTail count program prefixed).tail) (more : Nat)
      (config : Config Player L Γ),
      (fun law => law.bind (ProtocolState.behavioralStateStep program
        (Function.update profile who (graftPolicy who count program prefixed head rest))))^[
          count + more] (PMF.pure (ProtocolState.entry program config)) =
      (kernelChain who count program profile head prefixed config).bind fun reached =>
        ((fun law => law.bind (ProtocolState.behavioralStateStep
          (commitTail count program prefixed).tail
          (Function.update (commitTailProfile count program prefixed profile) who rest)))^[more]
          (PMF.pure (ProtocolState.entry _ reached))).map (commitTail count program prefixed).lift
  := by
  intro count
  induction count with
  | zero =>
      intro Γ names program profile prefixed head rest more config
      simp only [Nat.zero_add, kernelChain, PMF.pure_bind, commitTail, PMF.map_id]
      rfl
  | succ count ih =>
      intro Γ names program profile prefixed head rest more config
      cases program with
      | ret _ => exact prefixed.elim
      | sample _ _ _ _ => exact prefixed.elim
      | reveal _ _ _ _ _ _ _ => exact prefixed.elim
      | @commit Γ names name owner payload fresh guard next =>
          rw [show count + 1 + more = (count + more) + 1 by omega,
            ProtocolState.behavioralStatePrefix_commit, afterCommit_update,
            commitKernel_update_head profile who
              (graftPolicy who (count + 1) (.commit name owner fresh guard next) prefixed head rest)
              head rfl]
          simp only [kernelChain]
          rw [PMF.bind_bind]
          apply bind_congr_on_support _
          intro choice _
          rw [show (graftPolicy who (count + 1) (.commit name owner fresh guard next) prefixed
              head rest).2 = graftPolicy who count next prefixed head.2 rest from rfl,
            ih next (afterCommit profile) prefixed head.2 rest more, PMF.map_bind]
          apply bind_congr_on_support _
          intro reached _
          rw [PMF.map_comp]
          rfl


/-- **The source run through leading commitments.** The source run of a
profile is the chain of its kernels through the leading commitments followed by
the residual source run. -/
theorem iterate_listChain_all [Fintype Player] :
    ∀ (count : Nat) {Γ : SourceCtx Player L} {names : Finset VarId}
      (program : SourceProgram Player L Γ names) (profile : BehavioralProfile program)
      (prefixed : CommitPrefix program count) (more : Nat) (config : Config Player L Γ),
      (fun law => law.bind (ProtocolState.behavioralStateStep program profile))^[count + more]
          (PMF.pure (ProtocolState.entry program config)) =
        (listChain (fun _ => True) count program profile prefixed config []).bind
          fun reached =>
          ((fun law => law.bind (ProtocolState.behavioralStateStep
            (commitTail count program prefixed).tail
            (commitTailProfile count program prefixed profile)))^[more]
            (PMF.pure (ProtocolState.entry _ reached))).map (commitTail count program prefixed).lift
  := by
  intro count
  induction count with
  | zero =>
      intro Γ names program profile prefixed more config
      simp only [Nat.zero_add, listChain, PMF.pure_bind, commitTail, PMF.map_id]
      rfl
  | succ count ih =>
      intro Γ names program profile prefixed more config
      cases program with
      | ret _ => exact prefixed.elim
      | sample _ _ _ _ => exact prefixed.elim
      | reveal _ _ _ _ _ _ _ => exact prefixed.elim
      | @commit Γ names name owner payload fresh guard next =>
          rw [show count + 1 + more = (count + more) + 1 by omega,
            ProtocolState.behavioralStatePrefix_commit]
          simp only [listChain, ↓reduceIte]
          rw [PMF.bind_bind]
          apply bind_congr_on_support _
          intro choice _
          rw [ih next (afterCommit profile) prefixed more, PMF.map_bind]
          apply bind_congr_on_support _
          intro reached _
          rw [PMF.map_comp]
          rfl

end Vegas
