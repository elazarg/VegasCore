/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.Honest
import Vegas.Source.ProtocolTermination

/-! # Sequences of revelations of initialized commitments

`RevealOnly` is a property of existing source syntax. It introduces no executor,
admission mode, or restriction on disclosure choices. Owners may recur, and the
initial state may contain arbitrarily correlated private data. Validity of the
initial bindings is a separate setup premise.

The existing open-obligation index accounts for every reveal. From an empty
guard registry, every disclosure simply publishes the bound result or failure;
no guard condition has to be supplied by an analysis of this class.
-/

noncomputable section

namespace Vegas.State

variable {Player : Type} {L : IExpr} {Γ : SourceCtx Player L}

/-- Every commitment cell contains an actual value. This is an initial-state
premise for the reveal service, not a restriction on disclosure or payoffs. -/
def BindingsOpenable (state : State L Γ) : Prop :=
  ∀ {name owner payload} (ref : HasVar Γ name (.commitment owner payload)),
    ∃ value, state.get ref = .success value

/-- Adding a publication result preserves all existing commitment meanings,
whether the publication succeeded, was withheld, or failed a guard. -/
theorem BindingsOpenable.cons_publication {state : State L Γ}
    (openable : state.BindingsOpenable) (name : VarId) (payload : L.Ty)
    (result : PublicationResult (L.Val payload)) :
    BindingsOpenable (Env.cons (Val := CellVal (Player := Player) L) (x := name)
      (τ := .publication payload) result state) := by
  intro readName owner readPayload ref
  cases ref with
  | there prior => exact openable prior

end Vegas.State

namespace Vegas.SourceProgram

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- A fixed sequence of reveals followed by settlement, with no new bindings
or chance instructions. Disclosure and withholding are both still legal. -/
def RevealOnly : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    SourceProgram Player L Γ O → Prop
  | _, _, .ret _ => True
  | _, _, .reveal _ _ _ _ _ _ next => RevealOnly next
  | _, _, .sample .. | _, _, .commit .. => False

theorem RevealOnly.instructionCount_eq_card {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (reveals : RevealOnly program) :
    instructionCount program = O.card := by
  induction program with
  | ret payoffs => rfl
  | sample name fresh law next ih => exact reveals.elim
  | commit name owner fresh guard next ih => exact reveals.elim
  | @reveal context openNames published owner name payload fresh source unresolved next ih =>
      change instructionCount next + 1 = openNames.card
      rw [ih reveals]
      exact Finset.card_erase_add_one unresolved

omit [IExpr.ResultTypes L] in
theorem revealSuccessor_registry_empty {Γ : SourceCtx Player L}
    {name : VarId} {owner : Player} {payload : L.Ty} (published : VarId)
    (source : HasVar Γ name (.commitment owner payload))
    (config : Config Player L Γ) (empty : config.registry = []) (disclose : Bool) :
    (revealSuccessor published source config disclose).registry = [] := by
  simp only [revealSuccessor, empty, Registry.weaken, List.map_nil]

omit [IExpr.ResultTypes L] in
/-- An empty retained registry makes the actual source reveal kernel the
opening/withholding choice; this does not assume the binding is openable. -/
theorem revealSuccessor_result_of_registry_empty {Γ : SourceCtx Player L}
    {name : VarId} {owner : Player} {payload : L.Ty} (published : VarId)
    (source : HasVar Γ name (.commitment owner payload))
    (config : Config Player L Γ) (empty : config.registry = []) (disclose : Bool) :
    (revealSuccessor published source config disclose).state.get .here =
      if disclose then config.state.get source else .failure := by
  simp only [revealSuccessor, empty, Registry.completedBy, List.filter_nil, List.map_nil,
    List.all_nil, ↓reduceIte]
  rfl

omit [IExpr.ResultTypes L] in
/-- Revelation never invalidates a commitment, including other commitments
owned by the same player. The statement needs no guard-acceptance premise. -/
theorem revealSuccessor_bindingsOpenable {Γ : SourceCtx Player L}
    {name : VarId} {owner : Player} {payload : L.Ty} (published : VarId)
    (source : HasVar Γ name (.commitment owner payload))
    (config : Config Player L Γ) (openable : config.state.BindingsOpenable)
    (disclose : Bool) :
    (revealSuccessor published source config disclose).state.BindingsOpenable :=
  openable.cons_publication published payload _

/-- Every supported reveal-only continuation retains successful commitment
meanings. This includes every source policy and every withholding choice. -/
theorem RevealOnly.runFrom_bindingsOpenable {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (reveals : program.RevealOnly)
    (profile : BehavioralProfile program) (config : Config Player L Γ)
    (openable : config.state.BindingsOpenable) (terminal : State L program.terminalCtx)
    (supported : terminal ∈ (runFrom program profile config).support) :
    terminal.BindingsOpenable := by
  induction program with
  | ret payoffs =>
      have same : terminal = config.state := by simpa [runFrom, runWith] using supported
      rw [same]
      exact @openable
  | sample name fresh law next ih => exact reveals.elim
  | commit name owner fresh guard next ih => exact reveals.elim
  | reveal published owner name fresh source unresolved next ih =>
      rw [runFrom_reveal, FinDist.support_bind] at supported
      obtain ⟨disclose, _chosen, continued⟩ := Set.mem_iUnion₂.mp supported
      exact ih reveals (afterReveal profile) (revealSuccessor published source config disclose)
        (revealSuccessor_bindingsOpenable published source config openable disclose)
        terminal continued

/-- No source policy can create a guard obligation in a reveal-only suffix.
The result covers withheld publications and every subsequent continuation. -/
theorem RevealOnly.guardsAcceptFrom {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (reveals : RevealOnly program)
    (profile : BehavioralProfile program) (config : Config Player L Γ)
    (empty : config.registry = []) : GuardsAcceptFrom program profile config := by
  induction program with
  | ret payoffs => trivial
  | sample name fresh law next ih => exact reveals.elim
  | commit name owner fresh guard next ih => exact reveals.elim
  | reveal published owner name fresh source unresolved next ih =>
      constructor
      · intro value bound
        simp only [empty, Registry.completedBy, List.filter_nil, List.map_nil, List.all_nil]
      · intro disclose supported
        exact ih reveals (afterReveal profile) (revealSuccessor published source config disclose)
          (revealSuccessor_registry_empty published source config empty disclose)

end Vegas.SourceProgram
