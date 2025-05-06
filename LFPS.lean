
import Mathlib.Data.List.Basic
import Mathlib.Tactic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Use


--- Inductive Definition for Terms
inductive Term
| var : String → Term
| placeholder : Term   -- Placeholder for generalizing Ext


--- Inductive Definition for Formulas
inductive Formula
| bot : Formula
| var : String → Formula
| and : Formula → Formula → Formula
| or : Formula → Formula → Formula
| imp : Formula → Formula → Formula
| iff :  Formula → Formula → Formula
| neg : Formula → Formula
| pred : String → List Term → Formula
| forall_ : String → Formula → Formula
| exists_ : String → Formula → Formula
| diamond : List (String × Nat) → Formula → Formula
| box : List (String × Nat) → Formula → Formula
| eq : Term → Term → Formula

---Warning: this definition alone doesn't block quantifying in, although quantifying in is (importantly) not allowed in the language of logical possibility proposed in LFPS


def strip_arity (ℒ : List (String × Nat)) : List String :=
  ℒ.map Prod.fst



--- Decidable Equality for String
instance : DecidableEq String := inferInstance

--- Notation for Modal Operators
notation "◇_{" rs "} " φ => Formula.diamond rs φ
notation "□_{" rs "} " φ => Formula.box rs φ
notation:70 φ " ⋀ " ψ => Formula.and φ ψ
notation:65 φ " ⋁ " ψ => Formula.or φ ψ
notation:60 φ " ⇒ " ψ => Formula.imp φ ψ
notation:55 φ " ⇔ " ψ => Formula.iff φ ψ
notation "!" φ => Formula.neg φ
notation "A" x ", " φ => Formula.forall_ x φ
notation "E" x ", " φ => Formula.exists_ x φ




-- First-order logic domain
universe u
variable {U : Type u} -- U represents the domain of quantification
variable (P Q P1 P2 P3 P4 : U → Prop)  -- Unary predicate
variable (R S R1 R2 R3 R4 : U → U → Prop)  -- Binary predicate
variable (𝓛 : List (U → Prop))  --list of unary predicates
variable (𝓛₂ : List (U → U → Prop))   --list of binary predicates



-- Defining modal operators for LEAN native propsoition version of my sentences: possibility and necessity content restricted




inductive possibly (ℒ : List String) (P : Prop) : Prop
| intro : P → possibly ℒ P

inductive necessarily (ℒ : List String) (P : Prop) : Prop
| intro : P → necessarily ℒ P


--- BEq Implementation for Term (No change needed)
instance : BEq Term where
  beq t1 t2 :=
    match t1, t2 with
    | Term.var v1, Term.var v2 => v1 == v2
    | Term.placeholder, Term.placeholder => true
    | _, _ => false


-- Helper Function for Recursively Comparing Formulas
def beq_formula : Formula → Formula → Bool
| Formula.bot, Formula.bot => true
| Formula.var v1, Formula.var v2 => v1 == v2
| Formula.and φ₁ ψ₁, Formula.and φ₂ ψ₂ => 
    beq_formula φ₁ φ₂ && beq_formula ψ₁ ψ₂
| Formula.or φ₁ ψ₁, Formula.or φ₂ ψ₂ => 
    beq_formula φ₁ φ₂ && beq_formula ψ₁ ψ₂
| Formula.imp φ₁ ψ₁, Formula.imp φ₂ ψ₂ => 
    beq_formula φ₁ φ₂ && beq_formula ψ₁ ψ₂
| Formula.neg φ₁, Formula.neg φ₂ => 
    beq_formula φ₁ φ₂
| Formula.pred r1 args1, Formula.pred r2 args2 => 
    (r1 == r2) && (List.all₂ BEq.beq args1 args2)
| Formula.forall_ x₁ φ₁, Formula.forall_ x₂ φ₂ => 
    (x₁ == x₂) && beq_formula φ₁ φ₂
| Formula.exists_ x₁ φ₁, Formula.exists_ x₂ φ₂ => 
    (x₁ == x₂) && beq_formula φ₁ φ₂
| Formula.box rels1 φ₁, Formula.box rels2 φ₂ => 
    (rels1 == rels2) && beq_formula φ₁ φ₂
| Formula.diamond rels1 φ₁, Formula.diamond rels2 φ₂ => 
    (rels1 == rels2) && beq_formula φ₁ φ₂
| _, _ => false


-- BEq Implementation for Formula (Using Helper Function)
instance : BEq Formula where
  beq := beq_formula


-- Pretty Printing for Term
instance : ToString Term where
  toString t :=
    match t with
    | Term.var v => v
    | Term.placeholder => "_"


--- Pretty Printing for Formula

private def termToString : Term → String
  | Term.var v       => v
  | Term.placeholder => "_"


instance : ToString Formula where
  toString :=
    let rec aux : Formula → String :=
      fun
      | Formula.bot => "⊥"
      | Formula.var v => v
      | Formula.and φ ψ => "(" ++ aux φ ++ " ⋀ " ++ aux ψ ++ ")"
      | Formula.or φ ψ => "(" ++ aux φ ++ " ⋁ " ++ aux ψ ++ ")"
      | Formula.imp φ ψ => "(" ++ aux φ ++ " ⇒ " ++ aux ψ ++ ")"
      | Formula.iff φ ψ => "(" ++ aux φ ++ " ⇔ " ++ aux ψ ++ ")"
      | Formula.neg φ => "!" ++ aux φ
      | Formula.pred r args =>
          r ++ "(" ++ String.intercalate ", " (args.map termToString) ++ ")"
      | Formula.forall_ x φ => "A " ++ x ++ ", " ++ aux φ
      | Formula.exists_ x φ => "E " ++ x ++ ", " ++ aux φ
      | Formula.diamond rs φ =>
          "◇_{" ++ String.intercalate ", " (rs.map Prod.fst) ++ "} " ++ aux φ
      | Formula.box rs φ =>
          "□_{" ++ String.intercalate ", " (rs.map Prod.fst) ++ "} " ++ aux φ
      | Formula.eq t₁ t₂  => termToString t₁ ++ " = " ++ termToString t₂
   aux







-- Assume U is the type of objects in your domain
-- Uninterpreted Predicate Symbols with Explicit Type Parameter
variable {U : Type}[Inhabited U]


-- Assignment Function for Variables
def Assignment (U : Type U)[Inhabited U] := String → U



-- Now provide an Inhabited instance for Assignment U
instance [Inhabited U] : Inhabited (Assignment U) where
  default := λ _ => default  -- Maps every variable to the default value of U


-- First, collect all predicate symbols from a formula
def collect_predicates : Formula → List String
| Formula.bot => []
| Formula.var _ => []
| Formula.and φ ψ => collect_predicates φ ++ collect_predicates ψ
| Formula.or φ ψ => collect_predicates φ ++ collect_predicates ψ
| Formula.imp φ ψ => collect_predicates φ ++ collect_predicates ψ
| Formula.iff φ ψ => collect_predicates φ ++ collect_predicates ψ
| Formula.neg φ => collect_predicates φ
| Formula.pred r _ => [r]
| Formula.forall_ _ φ => collect_predicates φ
| Formula.exists_ _ φ => collect_predicates φ
| Formula.diamond _ φ => collect_predicates φ
| Formula.box _ φ => collect_predicates φ
| Formula.eq _ _ => []

-- Collect all predicates from a list of formulas
def collect_predicates_from_list : List Formula → List String
| [] => []
| (φ :: rest) => collect_predicates φ ++ collect_predicates_from_list rest

-- Remove duplicates from a list
def remove_duplicates (xs : List String) : List String :=
  xs.foldl (λ acc x => if x ∈ acc then acc else acc ++ [x]) []



-- Transform formula to Lean proposition using Lean predicate variables
def to_lean_prop
  {σ : Type} [Inhabited σ]
  (P₀ : Formula → Prop)
  (P₁ : String → σ → Prop)
  (P₂ : String → σ → σ → Prop)
  (σ₁ : Assignment σ) : Formula → Prop
| Formula.bot => False
| Formula.var s => P₀ (Formula.var s)  -- propositional variables
| Formula.and φ ψ => to_lean_prop  P₀ P₁ P₂ σ₁ φ ∧ to_lean_prop P₀ P₁ P₂ σ₁ ψ 
| Formula.or φ ψ => to_lean_prop  P₀ P₁ P₂ σ₁ φ ∨ to_lean_prop  P₀ P₁ P₂ σ₁ ψ
| Formula.imp φ ψ => to_lean_prop  P₀ P₁ P₂ σ₁ φ  → to_lean_prop  P₀ P₁ P₂ σ₁ ψ
| Formula.iff φ ψ => to_lean_prop  P₀ P₁ P₂ σ₁ φ  ↔ to_lean_prop  P₀ P₁ P₂ σ₁ ψ
| Formula.neg φ => ¬ to_lean_prop  P₀ P₁ P₂ σ₁ φ
| Formula.pred r [Term.var x] => P₁ r (σ₁ x)
| Formula.pred r [Term.var x, Term.var y] => P₂ r (σ₁ x) (σ₁ y)
| Formula.pred _ _ => False  -- fallback for malformed arities
| Formula.forall_ x φ => ∀ (u : σ), to_lean_prop P₀ P₁ P₂ (Function.update σ₁ x u) φ
| Formula.exists_ x φ => ∃ (u : σ), to_lean_prop P₀ P₁ P₂ (Function.update σ₁ x u) φ
| Formula.box ℒ φ => P₀ (Formula.box ℒ φ)  -- treat modal formulas as atoms
| Formula.diamond ℒ φ => P₀ (Formula.diamond ℒ φ)
| Formula.eq (Term.var x) (Term.var y) => σ₁ x = σ₁ y
| Formula.eq _ _ => False  -- unsupported identity terms



def FOL_equiv_all : Formula → Formula → Prop
| φ, ψ =>
  ∀ {σ : Type} [Inhabited σ],
    ∀ (P₀ : Formula → Prop)
      (P₁ : String → σ → Prop)
      (P₂ : String → σ → σ → Prop)
      (σ₁ : Assignment σ),
    to_lean_prop P₀ P₁ P₂ σ₁ φ ↔ to_lean_prop P₀ P₁ P₂ σ₁ ψ




--- orList  and andList Utility Function
@[simp] def orList : List Formula → Formula
| [] => Formula.bot
| [f] => f
| f :: fs => Formula.or f (orList fs)

@[simp] def andList : List Formula → Formula
| [] => Formula.bot
| [f] => f
| f :: fs => Formula.and f (andList fs)

---forall_many  and exists_many utility functions

def Formula.forall_many : List String → Formula → Formula
| [],     φ => φ
| x :: xs, φ => Formula.forall_ x (Formula.forall_many xs φ)

@[simp] def Formula.exists_many : List String → Formula → Formula
| [], φ => φ
| x :: xs, φ => Formula.exists_ x (Formula.exists_many xs φ)

-- Manually insert an element at a given index
@[simp] def insertAt {α : Type} (lst : List α) (idx : Nat) (elem : α) : List α :=
  let (before, after) := lst.splitAt idx
  before ++ [elem] ++ after

-- Utility: Generate a list of variable names ["x0", "x1", ..., "x(n-1)"]
@[simp] def genVars (n : Nat) : List String :=
  List.range n |>.map (λ i => "x" ++ toString i)

-- Generalized Ext Function
@[simp] def Ext (ℒ : List (String × Nat)) (y : String) : Formula :=
  let fs := ℒ.map (λ (rel, arity) =>
    -- Handle relations of arbitrary arity
    if arity > 0 then
      -- Generate the required variables for quantification
      let vars := genVars (arity - 1)
      -- Generate disjuncts for each position of y
      let disjuncts := List.range arity |>.map (λ j =>
        -- Insert y at position j
        let args_with_y := insertAt (vars.map Term.var) j (Term.var y)
        -- Construct the predicate
        let pred := Formula.pred rel args_with_y
        pred
      )
      -- Combine the disjuncts with orList
      let combined_disjuncts := orList disjuncts
      -- Quantify over all variables except y, starting from the last
      vars.reverse.foldl (λ acc x => Formula.exists_ x acc) combined_disjuncts
    else 
      Formula.bot  -- Ignore relations of arity 0
  )
  -- Combine all quantified formulas with orList (now we have a List Formula)
  orList fs




-- is_sentence to check if a formula is a sentence (i.e., no free variables)
@[simp] def is_sentence : Formula → List String → Bool
| Formula.bot, _ => true
| Formula.var _, _ => false  -- Propositional variables are not sentences
| Formula.and φ ψ, ctx => is_sentence φ ctx && is_sentence ψ ctx
| Formula.or φ ψ, ctx => is_sentence φ ctx && is_sentence ψ ctx
| Formula.imp φ ψ, ctx => is_sentence φ ctx && is_sentence ψ ctx
| Formula.iff φ ψ, ctx => is_sentence φ ctx && is_sentence ψ ctx
| Formula.neg φ, ctx => is_sentence φ ctx
| Formula.pred _ args, ctx =>
    args.all (λ t => match t with
                    | Term.var v => ctx.elem v
                    | _ => true
                  )
| Formula.forall_ x φ, ctx =>
    is_sentence φ (x :: ctx)  -- Correctly adding the bound variable
| Formula.exists_ x φ, ctx =>
    is_sentence φ (x :: ctx)  -- Same for existential quantifier
| Formula.diamond _ φ, _ => is_sentence φ []  -- Empty context for Diamond
| Formula.box _ φ, _ => is_sentence φ []       -- Empty context for Box
| Formula.eq t₁ t₂, ctx =>
    let check_term := λ t => match t with
      | Term.var v => ctx.elem v
      | _ => true  -- placeholder or constants assumed safe
    check_term t₁ && check_term t₂



@[simp] def FOL_entails_all (Γ : List Formula) (φ : Formula) : Prop :=
  ∀ {σ : Type} [Inhabited σ]
    (P₀ : Formula → Prop)
    (P₁ : String → σ → Prop)
    (P₂ : String → σ → σ → Prop)
    (σ₁ : Assignment σ),
    (∀ γ ∈ Γ, to_lean_prop P₀ P₁ P₂ σ₁ γ) → to_lean_prop P₀ P₁ P₂ σ₁ φ



def appears_free_in (x : String) : Formula → Bool
| Formula.bot => false
| Formula.var v => v = x
| Formula.and φ ψ => appears_free_in x φ || appears_free_in x ψ
| Formula.or φ ψ => appears_free_in x φ || appears_free_in x ψ
| Formula.imp φ ψ => appears_free_in x φ || appears_free_in x ψ
| Formula.iff φ ψ => appears_free_in x φ || appears_free_in x ψ
| Formula.neg φ => appears_free_in x φ
| Formula.pred _ args => args.any (λ t => match t with
    | Term.var v => v = x
    | _ => false)
| Formula.forall_ y φ => if y = x then false else appears_free_in x φ
| Formula.exists_ y φ => if y = x then false else appears_free_in x φ
| Formula.diamond _ φ => appears_free_in x φ
| Formula.box _ φ => appears_free_in x φ
| Formula.eq t₁ t₂ => 
    match t₁, t₂ with
    | Term.var v₁, Term.var v₂ => x = v₁ || x = v₂
    | Term.var v, _ => x = v
    | _, Term.var v => x = v
    | _, _ => false




/--
  `restrict_formula_explicitly_core ℒ inModal φ` transforms the formula `φ` so that:
  - If `inModal = false`, all ∀ and ∃ quantifiers are “content-restricted” 
    by inserting `Ext ℒ x` into them.
  - If `inModal = true`, we do NOT insert content restrictions (since we are 
    inside a box/diamond).
  - For diamonds and boxes, we switch `inModal` to `true` for subformulas.
--/
@[simp] def restrict_formula_explicitly_core 
    (ℒ : List (String × Nat)) 
    (inModal : Bool) 
    : Formula → Formula
| Formula.bot => Formula.bot
| Formula.var v => Formula.var v
| Formula.and φ ψ => Formula.and
    (restrict_formula_explicitly_core ℒ inModal φ)
    (restrict_formula_explicitly_core ℒ inModal ψ)
| Formula.or φ ψ => Formula.or
    (restrict_formula_explicitly_core ℒ inModal φ)
    (restrict_formula_explicitly_core ℒ inModal ψ)
| Formula.imp φ ψ => Formula.imp
    (restrict_formula_explicitly_core ℒ inModal φ)
    (restrict_formula_explicitly_core ℒ inModal ψ)
| Formula.iff φ ψ => Formula.iff
    (restrict_formula_explicitly_core ℒ inModal φ)
    (restrict_formula_explicitly_core ℒ inModal ψ)
| Formula.neg φ =>
    Formula.neg (restrict_formula_explicitly_core ℒ inModal φ)
| Formula.pred r args =>
    Formula.pred r args  -- No change for atomic predicates
| Formula.forall_ x body =>
  if inModal then
    -- Do not insert content restrictions inside modal subformulas
    Formula.forall_ x (restrict_formula_explicitly_core ℒ inModal body)
  else
    -- Outside modal context: ∀ x φ becomes ∀ x (Ext(ℒ, x) → φ)
    Formula.forall_ x (Formula.imp (Ext ℒ x) (restrict_formula_explicitly_core ℒ inModal body))
| Formula.exists_ x body =>
  if inModal then
    -- Same as above
    Formula.exists_ x (restrict_formula_explicitly_core ℒ inModal body)
  else
    -- Outside modal context: ∃ x φ becomes ∃ x (Ext(ℒ, x) ∧ φ)
    Formula.exists_ x (Formula.and (Ext ℒ x) (restrict_formula_explicitly_core ℒ inModal body))
| Formula.diamond rels φ =>
    -- Once we enter a diamond, subformulas are in modal context
    Formula.diamond rels (restrict_formula_explicitly_core ℒ true φ)
| Formula.box rels φ =>
    -- Likewise for box
    Formula.box rels (restrict_formula_explicitly_core ℒ true φ)
| Formula.eq t₁ t₂ => Formula.eq t₁ t₂

/--
  Main user function:
  Applies content restriction to *outer* quantifiers of formula `φ` 
  by inserting `Ext(ℒ, x)` at each ∀x or ∃x, stopping once we reach 
  a diamond or box subformula.
--/
@[simp]  def restrict_formula_explicitly 
    (ℒ : List (String × Nat)) 
    (φ : Formula) 
    : Formula :=
  restrict_formula_explicitly_core ℒ false φ


-- Utility Function to Check Subset for Lists
@[simp]def list_subset (ℒ' ℒ : List String) : Bool :=
  (ℒ'.toFinset ⊆ ℒ.toFinset)



-- is_content_restricted checks if a formula is content restricted to exactly a list of relations ℒ
@[simp] def is_content_restricted : Formula → List (String × Nat) → List String → Bool
| Formula.bot, _, _ => true  -- Clause 1
| Formula.var _, _, _ => false  -- Propositional variables are not content-restricted
| Formula.pred r args, ℒ, ctx =>
    (r ∈ ℒ.map Prod.fst) && args.all (λ t => match t with
                                | Term.var v => v ∈ ctx
                                | _ => true
                              )  -- Clause 3
| Formula.and φ ψ, ℒ, ctx =>
    is_content_restricted φ ℒ ctx && is_content_restricted ψ ℒ ctx  -- Clause 4
| Formula.or φ ψ, ℒ, ctx =>
    is_content_restricted φ ℒ ctx && is_content_restricted ψ ℒ ctx  -- Clause 4
| Formula.imp φ ψ, ℒ, ctx =>
    is_content_restricted φ ℒ ctx && is_content_restricted ψ ℒ ctx  -- Clause 4
| Formula.neg φ, ℒ, ctx =>
    is_content_restricted φ ℒ ctx  -- Clause 4
| Formula.exists_ x (Formula.and ψ φ), ℒ, ctx =>
    -- Call Ext and check if the generated formula matches the first conjunct
    let expected_ext := Ext ℒ x
    (ψ == expected_ext) && is_content_restricted φ ℒ (x :: ctx)
| Formula.forall_ x (Formula.imp ψ φ), ℒ, ctx =>
    -- Call Ext and check if the generated formula matches the antecedent
    let expected_ext := Ext ℒ x
    (ψ == expected_ext) && is_content_restricted φ ℒ (x :: ctx)
| Formula.diamond ℒ' φ, ℒ, _ =>
    ℒ'.all (λ r => r ∈ ℒ) &&
    is_sentence φ [] 
| Formula.box ℒ' φ, ℒ, _ =>
    ℒ'.all (λ r => r ∈ ℒ) &&
    is_sentence φ [] 
| _, _, _ => false  -- Fallback for non-matching cases "


@[simp] def is_content_restricted_to (ℒ : List (String × Nat)) (φ : Formula) : Prop :=
  is_content_restricted φ ℒ []

@[simp] def is_implicitly_content_restricted_to (ℒ : List (String × Nat)) (φ : Formula) : Prop :=
  FOL_equiv_all φ (restrict_formula_explicitly ℒ φ) ∧
  is_content_restricted_to ℒ (restrict_formula_explicitly ℒ φ)


@[simp] def genIndexedVars (pre : String) (n : Nat) : List String :=
  List.range n |>.map (fun i => pre ++ toString i)



--Building Blocks for Simple Comprehension Rule

@[simp] def mentions_relation (r : String) : Formula → Bool
| Formula.bot => false
| Formula.var _ => false
| Formula.and φ ψ => mentions_relation r φ || mentions_relation r ψ
| Formula.or φ ψ => mentions_relation r φ || mentions_relation r ψ
| Formula.imp φ ψ => mentions_relation r φ || mentions_relation r ψ
| Formula.iff φ ψ => mentions_relation r φ || mentions_relation r ψ
| Formula.neg φ => mentions_relation r φ
| Formula.pred r' _ => r = r'
| Formula.forall_ _ φ => mentions_relation r φ
| Formula.exists_ _ φ => mentions_relation r φ
| Formula.diamond _ φ => mentions_relation r φ
| Formula.box _ φ => mentions_relation r φ
| Formula.eq _ _ => false




def instantiate_vars (φ : Formula) (vars : List String) : Formula :=
  φ  -- eventually this could plug in terms for placeholders



-- Helper: construct the expected comprehension body
def comprehension_body (Ψ φ : Formula) (R : String) (vars : List String) : Formula :=
  Formula.and Ψ (
    Formula.forall_many vars (
      Formula.iff
        (Formula.pred R (vars.map Term.var))
        φ
    )
  )

--- Building Blocks for Cutback

-- (∃x) P(x)
@[simp] def cutback_exists (P : String) : Formula :=
  Formula.exists_ "x" (Formula.pred P [Term.var "x"])

-- (∀x) Ext(ℒ, x) → P(x)
@[simp] def cutback_ext (ℒ : List (String × Nat)) (P : String) : Formula :=
  Formula.forall_ "x" (
    Formula.imp (Ext ℒ "x") (Formula.pred P [Term.var "x"])
  )

-- (∀x) P(x)
@[simp] def cutback_forall (P : String) : Formula :=
  Formula.forall_ "x" (Formula.pred P [Term.var "x"])

--- Building Blocks for Relabeling

@[simp] def replace_relation (r : String) (relabel : List (String × String)) : String :=
  match relabel.find? (λ p => p.1 = r) with
  | some (_, new_r) => new_r
  | none => r

@[simp] def Formula.rename_relations (relabel : List (String × String)) : Formula → Formula
  | Formula.bot => Formula.bot
  | Formula.var v => Formula.var v
  | Formula.and φ ψ => Formula.and (Formula.rename_relations relabel φ) (Formula.rename_relations relabel ψ)
  | Formula.or φ ψ => Formula.or (Formula.rename_relations relabel φ) (Formula.rename_relations relabel ψ)
  | Formula.imp φ ψ => Formula.imp (Formula.rename_relations relabel φ) (Formula.rename_relations relabel ψ)
  | Formula.iff φ ψ => Formula.iff (Formula.rename_relations relabel φ) (Formula.rename_relations relabel ψ)
  | Formula.neg φ => Formula.neg (Formula.rename_relations relabel φ)
  | Formula.pred r args => Formula.pred (replace_relation r relabel) args
  | Formula.forall_ x φ => Formula.forall_ x (Formula.rename_relations relabel φ)
  | Formula.exists_ x φ => Formula.exists_ x (Formula.rename_relations relabel φ)
  | Formula.diamond ℒ φ => Formula.diamond ℒ (Formula.rename_relations relabel φ)
  | Formula.box ℒ φ => Formula.box ℒ (Formula.rename_relations relabel φ)
  | Formula.eq t₁ t₂ => Formula.eq t₁ t₂

@[simp] def extract_relabeling_pairs (old new : List String) : Option (List (String × String)) :=
  if old.length ≠ new.length then none
  else some (old.zip new)

-- Building blocks for Modal Comprehension 


/--
  Abbreviated “unique existence” in our object language:
  ∃! x. φ(x)  :=  ∃ x. φ(x) ∧ ∀ x. (φ(x) → x = x)
--/
@[simp] def Formula.exists_unique (x : String) (φ : Formula) : Formula :=
  Formula.exists_ x (
    Formula.and φ (
      Formula.forall_ x (
        Formula.imp φ (Formula.eq (Term.var x) (Term.var x))
      )
    )
  )

/--
  Abbreviated “unique existence” for n‑tuples:
  ∃! vars. R(vars)
--/

-- ∃!tuple vars. Q(vars)
@[simp]
def Formula.exists_unique_many (R : String) (n : Nat) : Formula :=
  let vars :=  genVars n                           
  let pred := Formula.pred R (vars.map Term.var)

  let exists_clause := Formula.exists_many vars pred         -- ∃v0 v1... R(vs)

  let vars₁ := vars.map (λ x => x ++ "_1")                   -- ["v0_1", "v1_1"]
  let vars₂ := vars.map (λ x => x ++ "_2")                   -- ["v0_2", "v1_2"]
  let pred₁ := Formula.pred R (vars₁.map Term.var)
  let pred₂ := Formula.pred R (vars₂.map Term.var)

  let eqs := List.zipWith (λ x y => Formula.eq (Term.var x) (Term.var y)) vars₁ vars₂
  let all_eqs := andList eqs

  let uniqueness :=
    Formula.forall_many (vars₁ ++ vars₂) (
      Formula.imp (Formula.and pred₁ pred₂) all_eqs
    )

  Formula.and exists_clause uniqueness


def unique_witness_formula : Formula :=
  Formula.exists_unique_many "witness" 2

#eval unique_witness_formula

def all_in_Ext (ℒ : List (String × Nat)) (vars : List String) : Formula :=
  andList (vars.map (λ v => Ext ℒ v))

def restrict_R_to_structure (ℒ : List (String × Nat)) (R : String) (vars : List String) (φ : Formula) : Formula :=
  Formula.iff 
    (Formula.pred R (vars.map Term.var))
    (Formula.and (all_in_Ext ℒ vars) φ)

def modal_comprehension_formula 
  (ℒ : List (String × Nat)) 
  (Ψ φ : Formula) 
  (R Q : String) 
  (n : Nat) : Formula :=
  
  let vars := genVars n
  let uniqueQ := Formula.exists_unique_many Q n
  let inner := Formula.exists_many vars (
                  Formula.and
                    (Formula.pred Q (vars.map Term.var))
                    (restrict_R_to_structure ℒ R vars φ)
               )
  let boxed := Formula.box (ℒ ++ [(R, n)]) (Formula.imp uniqueQ inner)
  Formula.diamond ℒ (Formula.and Ψ boxed)




--- Building Blocks for Infinity
-- Clause 1: ∀x ∀y ∀y'. S(x,y) ∧ S(x,y') → y = y'
def infinity_clause_1 : Formula :=
  Formula.forall_many ["x", "y", "y'"] (
    Formula.imp
      (Formula.and
        (Formula.pred "S" [Term.var "x", Term.var "y"])
        (Formula.pred "S" [Term.var "x", Term.var "y'"]))
      (Formula.eq (Term.var "y") (Term.var "y'"))
  )

-- Clause 2: ∀x ∀y ∀x'. S(x,y) ∧ S(x',y) → x = x'
def infinity_clause_2 : Formula :=
  Formula.forall_many ["x", "y", "x'"] (
    Formula.imp
      (Formula.and
        (Formula.pred "S" [Term.var "x", Term.var "y"])
        (Formula.pred "S" [Term.var "x'", Term.var "y"]))
      (Formula.eq (Term.var "x") (Term.var "x'")
  ))

-- Clause 3: ∃!x ∃y. S(x,y) ∧ ∀y. ¬S(y,x)
def infinity_clause_3 : Formula :=
  let inner :=
    Formula.exists_ "y" (
      Formula.and
        (Formula.pred "S" [Term.var "x", Term.var "y"])
        (Formula.forall_ "y" (Formula.neg (Formula.pred "S" [Term.var "y", Term.var "x"])))
    )
  Formula.exists_ "x" inner  -- ∃! could be mimicked if needed, but ∃ works here

-- Clause 4: ∀x. (∃y. S(y,x)) → (∃z. S(x,z))
def infinity_clause_4 : Formula :=
  Formula.forall_ "x" (
    Formula.imp
      (Formula.exists_ "y" (Formula.pred "S" [Term.var "y", Term.var "x"]))
      (Formula.exists_ "z" (Formula.pred "S" [Term.var "x", Term.var "z"]))
  )

-- Clause 5: ∀x ∀y. S(x,y) → ¬S(y,x)
def infinity_clause_5 : Formula :=
  Formula.forall_many ["x", "y"] (
    Formula.imp
      (Formula.pred "S" [Term.var "x", Term.var "y"])
      (Formula.neg (Formula.pred "S" [Term.var "y", Term.var "x"]))
  )

def infinity_axiom_body : Formula :=
  andList [
    infinity_clause_1,
    infinity_clause_2,
    infinity_clause_3,
    infinity_clause_4,
    infinity_clause_5
  ]

def infinity_axiom_modal : Formula :=
  Formula.diamond [("S", 2)] infinity_axiom_body

--- Building Blocks for Possible Powerset
-- Clause 1: ∀x. ¬(C(x) ∧ F(x))
def powerset_clause_1 (F C : String) : Formula :=
  Formula.forall_ "x" (
    Formula.neg (
      Formula.and
        (Formula.pred C [Term.var "x"])
        (Formula.pred F [Term.var "x"])
    )
  )

-- Clause 2: ∀x ∀y. (x ∈_C y) → (F(x) ∧ C(y))
def powerset_clause_2 (F C mem : String) : Formula :=
  Formula.forall_many ["x", "y"] (
    Formula.imp
      (Formula.pred mem [Term.var "x", Term.var "y"])
      (Formula.and
        (Formula.pred F [Term.var "x"])
        (Formula.pred C [Term.var "y"]))
  )

-- Clause 3: □_{F,C,mem}(∃x. C(x) ∧ ∀y. ((F(y) ∧ K(y)) ↔ y ∈_C x))
def powerset_clause_3 (F C mem : String) : Formula :=
  let inner :=
    Formula.exists_ "x" (
      Formula.and
        (Formula.pred C [Term.var "x"])
        (Formula.forall_ "y" (
          Formula.iff
            (Formula.and
              (Formula.pred F [Term.var "y"])
              (Formula.pred "K" [Term.var "y"]))
            (Formula.pred mem [Term.var "y", Term.var "x"])
        ))
    )
  Formula.box [(F,1), (C,1), (mem,2)] inner

-- Clause 4: ∀y ∀y'. (C(y) ∧ C(y') ∧ ¬(y = y')) → ∃x. ¬(x ∈_C y ↔ x ∈_C y')
def powerset_clause_4 (C mem : String) : Formula :=
  Formula.forall_many ["y", "y'"] (
    Formula.imp
      (Formula.and
        (Formula.and
          (Formula.pred C [Term.var "y"])
          (Formula.pred C [Term.var "y'"]))
        (Formula.neg (Formula.eq (Term.var "y") (Term.var "y'"))))
      (Formula.exists_ "x" (
        Formula.neg (
          Formula.iff
            (Formula.pred mem [Term.var "x", Term.var "y"])
            (Formula.pred mem [Term.var "x", Term.var "y'"])
        ))
  ))

def possible_powerset_body (F C mem : String) : Formula :=
  andList [
    powerset_clause_1 F C,
    powerset_clause_2 F C mem,
    powerset_clause_3 F C mem,
    powerset_clause_4 C mem
  ]

-- Building blocks for Choice

-- Unique existence: ∃! y. φ(y) := ∃ y. φ(y) ∧ ∀ y' (φ(y') → y' = y)
def exists_unique (vars : List String) (φ : Formula) : Formula :=
  match vars with
  | []      => φ
  | y :: ys =>
    Formula.exists_ y (
      Formula.and φ (
        Formula.forall_ y (
          Formula.imp φ (Formula.eq (Term.var y) (Term.var y))
        )
      )
    )  -- (simplified version — for now we assume m = 1)

-- Core body of the choice axiom
def choice_axiom_body
  (n m : Nat)
  (I R R_hat : String)
  (φ : Formula) : Formula :=

  let x_vars := List.range n |>.map (fun i => "x" ++ toString i)
  let y_vars := List.range m |>.map (fun j => "y" ++ toString j)

  let ext_tuple := x_vars ++ y_vars

  let totality_clause :=
    Formula.forall_many x_vars (
      Formula.imp
        (Formula.pred I (x_vars.map Term.var))
        (Formula.exists_many y_vars (
          Formula.pred R (ext_tuple.map Term.var)
        ))
    )

  let inclusion_clause :=
    Formula.forall_many ext_tuple (
      Formula.imp
        (Formula.pred R_hat (ext_tuple.map Term.var))
        (Formula.pred R (ext_tuple.map Term.var))
    )

  let uniqueness_clause :=
    Formula.forall_many x_vars (
      Formula.imp
        (Formula.pred I (x_vars.map Term.var))
        (Formula.exists_unique_many (R_hat) (n + m))  -- applies to full arity
  )


  Formula.and φ (Formula.and totality_clause (Formula.and inclusion_clause uniqueness_clause))


def choice_axiom_modal
  (L : List (String × Nat))
  (n m : Nat)
  (I R R_hat : String)
  (φ : Formula) : Formula :=
  Formula.diamond (L ++ [(I, n), (R, n + m)]) (choice_axiom_body n m I R R_hat φ)

namespace Formula

/-- Helper recursive function to track bound variables -/
def free_vars_core : Formula → List String → List String
| Formula.bot, _ => []
| Formula.var v, ctx => if v ∈ ctx then [] else [v]
| Formula.and φ ψ, ctx => free_vars_core φ ctx ++ free_vars_core ψ ctx
| Formula.or φ ψ, ctx => free_vars_core φ ctx ++ free_vars_core ψ ctx
| Formula.imp φ ψ, ctx => free_vars_core φ ctx ++ free_vars_core ψ ctx
| Formula.iff φ ψ, ctx => free_vars_core φ ctx ++ free_vars_core ψ ctx
| Formula.neg φ, ctx => free_vars_core φ ctx
| Formula.pred _ args, ctx =>
    args.foldl (fun acc t =>
      match t with
      | Term.var v => if v ∈ ctx then acc else v :: acc
      | _ => acc
    ) []
| Formula.forall_ x φ, ctx => free_vars_core φ (x :: ctx)
| Formula.exists_ x φ, ctx => free_vars_core φ (x :: ctx)
| Formula.diamond _ φ, _ => free_vars_core φ []     -- modal formulas are full sentences
| Formula.box _ φ, _ => free_vars_core φ []         -- likewise
| Formula.eq t₁ t₂, ctx =>
    let collect := λ t => match t with
      | Term.var v => if v ∈ ctx then [] else [v]
      | _ => []
    collect t₁ ++ collect t₂

/-- Public function: computes the list of free variables in a formula -/
def free_vars (φ : Formula) : List String :=
  (free_vars_core φ []).eraseDups



end Formula
--Building blocks for comprehension 

namespace Formula


/--
Helper for "big disjunction" in disjoint slices
--/
def big_or : List Formula → Formula
| []        => Formula.bot
| [f]       => f
| (f::fs)   => Formula.or f (big_or fs)


/--
  Given a list of old relations Rs and a list of corresponding new slice relations Rhats,
  rewrite a formula by replacing each occurrence of Rᵢ(t₁, …, tₙ) with R̂ᵢ(t₁, …, tₙ, x).

  That is, each Rᵢ is mapped to R̂ᵢ, and the indexing term (usually x) is appended at the end.

  Assumes Rs and Rhats are aligned lists of same length.

  We always add Term.var "x" as the index.

  map_relations : Apply a function to every atomic relation occurrence inside a formula.
 

  Traverse a Formula, replacing each atomic relation r(args)
  with (f r args).
  f : takes a relation name `r` and its argument list, returns a new Formula.
--/
def map_relations (f : String → List Term → Formula) : Formula → Formula
| Formula.bot               => Formula.bot
| Formula.var v             => Formula.var v
| Formula.pred r ts         => f r ts
| Formula.eq t1 t2          => Formula.eq t1 t2
| Formula.neg φ             => Formula.neg (map_relations f φ)
| Formula.and φ ψ           => Formula.and (map_relations f φ) (map_relations f ψ)
| Formula.or φ ψ            => Formula.or  (map_relations f φ) (map_relations f ψ)
| Formula.imp φ ψ           => Formula.imp (map_relations f φ) (map_relations f ψ)
| Formula.iff φ ψ           => Formula.iff (map_relations f φ) (map_relations f ψ)
| Formula.forall_ x φ       => Formula.forall_ x (map_relations f φ)
| Formula.exists_ x φ       => Formula.exists_ x (map_relations f φ)
| Formula.box ℒ φ           => Formula.box ℒ (map_relations f φ)
| Formula.diamond ℒ φ       => Formula.diamond ℒ (map_relations f φ)

/--
  Substitute free occurrences of variable `old` with `new` in a Term.
--/
def Term.substitute (old new : String) : Term → Term
| Term.var v => if v = old then Term.var new else Term.var v
| t          => t

/--
  Substitute free occurrences of variable `old` with `new` in a Formula.
  (Avoids capture: does not recurse under a binder for the same variable.)
--/
def substitute_var (φ : Formula) (old new : String) : Formula :=
  match φ with
  | Formula.bot           => Formula.bot
  | Formula.var v         => Formula.var v
  | Formula.pred r args   => Formula.pred r (args.map (Term.substitute old new))
  | Formula.eq t1 t2      => Formula.eq (Term.substitute old new t1) (Term.substitute old new t2)
  | Formula.neg φ₁        => Formula.neg (Formula.substitute_var φ₁ old new)
  | Formula.and φ₁ φ₂     => Formula.and (Formula.substitute_var φ₁ old new) (Formula.substitute_var φ₂ old new)
  | Formula.or φ₁ φ₂      => Formula.or  (Formula.substitute_var φ₁ old new) (Formula.substitute_var φ₂ old new)
  | Formula.imp φ₁ φ₂     => Formula.imp (Formula.substitute_var φ₁ old new) (Formula.substitute_var φ₂ old new)
  | Formula.iff φ₁ φ₂     => Formula.iff (Formula.substitute_var φ₁ old new) (Formula.substitute_var φ₂ old new)
  | Formula.forall_ x φ₁  => if x = old then Formula.forall_ x φ₁ else Formula.forall_ x (Formula.substitute_var φ₁ old new)
  | Formula.exists_ x φ₁  => if x = old then Formula.exists_ x φ₁ else Formula.exists_ x (Formula.substitute_var φ₁ old new)
  | Formula.box ℒ φ₁      => Formula.box ℒ (Formula.substitute_var φ₁ old new)
  | Formula.diamond ℒ φ₁  => Formula.diamond ℒ (Formula.substitute_var φ₁ old new)




def rename_relations_with_index (φ : Formula) (Rs Rhats : List (String × Nat)) : Formula :=
  φ.map_relations (λ r args =>
    match List.findIdx? (λ (p : String × Nat) => p.fst = r) Rs with
    | some idx =>
      let new_rhat := Rhats.get! idx
      Formula.pred new_rhat.fst ( [Term.var "x"] ++ args ) -- append index x
    | none => Formula.pred r args -- if relation not among Rs, leave untouched
  )



/--
  Builds the general amalgamation possibility sentence:

    ◇_L ( (∀x (I(x) → φ'(x))) ∧ (∀x y z (I(x) ∧ I(y) ∧ x ≠ y ∧ (⋁₁ⁿ (R'ᵢ(z,x) ∧ R'ᵢ(z,y))) →  Ext L z)) )

  where:
  - L is the background structure,
  - I is the indexing predicate (must appear in L),
  - Rs are the original relations appearing in φ,
  - R̂s are the new slice-relations,
  - φ is the original one-place formula.

  φ' is obtained from φ with each R_i replaced by Rhat_i(...,x), adding the slice index x appropriately.

--/
def amalgamation_axiom
  (L     : List (String × Nat))
  (I     : String)
  (Rs    : List (String × Nat))
  (Rhats : List (String × Nat))
  (φ     : Formula)
  : Formula :=
let φ' := φ.rename_relations_with_index Rs Rhats;
let per_x : Formula :=
  Formula.forall_ "x" (
    Formula.imp
      (Formula.pred I [Term.var "x"])
      φ'
  );
let disjoint_slices : Formula :=
  Formula.forall_many ["x","y","z"] (
    Formula.imp
      ( Formula.and
          (Formula.pred I [Term.var "x"])
          ( Formula.and
              (Formula.pred I [Term.var "y"])
              ( Formula.and
                  (Formula.neg (Formula.eq (Term.var "x") (Term.var "y")))
                  ( big_or (
                      List.map (λ r =>
                        Formula.and
                          (Formula.pred r.fst [Term.var "z", Term.var "x"])
                          (Formula.pred r.fst [Term.var "z", Term.var "y"]))
                      Rhats)
                  )
              )
          )
      )
      (Ext L "z")
  );
Formula.diamond L (Formula.and per_x disjoint_slices)



end Formula



---- PROOF RULES START HERE 

inductive NDProof : List Formula → Formula → Type where
  -- Assumption
  | assumption {Γ : List Formula} {φ : Formula}
      (h : φ ∈ Γ) : NDProof Γ φ

  -- Conjunction Introduction
  | andI {Γ φ ψ} (h1 : NDProof Γ φ) (h2 : NDProof Γ ψ) : NDProof Γ (Formula.and φ ψ)

  -- Conjunction Elimination
  | andE_left {Γ φ ψ} (h : NDProof Γ (Formula.and φ ψ)) : NDProof Γ φ
  | andE_right {Γ φ ψ} (h : NDProof Γ (Formula.and φ ψ)) : NDProof Γ ψ

  -- Disjunction Introduction
  | orI_left {Γ φ ψ} (h : NDProof Γ φ) : NDProof Γ (Formula.or φ ψ)
  | orI_right {Γ φ ψ} (h : NDProof Γ ψ) : NDProof Γ (Formula.or φ ψ)

  -- Disjunction Elimination
  | orE {Γ φ ψ χ}
      (h_or : NDProof Γ (Formula.or φ ψ))
      (h1 : NDProof (φ :: Γ) χ)
      (h2 : NDProof (ψ :: Γ) χ) : NDProof Γ χ

  -- Implication Introduction
  | impI {Γ φ ψ} (h : NDProof (φ :: Γ) ψ) : NDProof Γ (Formula.imp φ ψ)

  -- Implication Elimination
  | impE {Γ φ ψ} (h1 : NDProof Γ (Formula.imp φ ψ)) (h2 : NDProof Γ φ) : NDProof Γ ψ

  -- Negation Introduction
  | negI {Γ φ} (h : NDProof (φ :: Γ) Formula.bot) : NDProof Γ (Formula.neg φ)

  -- Negation Elimination
  | negE {Γ φ} (h1 : NDProof Γ (Formula.neg φ)) (h2 : NDProof Γ φ) : NDProof Γ Formula.bot

  -- Ex Falso Quodlibet
  | exFalso {Γ φ} (h : NDProof Γ Formula.bot) : NDProof Γ φ

  -- Universal Introduction
  | forallI {Γ x φ}
      (h : NDProof Γ φ)
      (h_x_not_free : ∀ ψ ∈ Γ, ¬ appears_free_in x ψ) : NDProof Γ (Formula.forall_ x φ)

  -- Universal Elimination
  | forallE {Γ x φ }
      (h : NDProof Γ (Formula.forall_ x φ)) : NDProof Γ φ

  -- Existential Introduction
  | existsI {Γ x φ }
      (h : NDProof Γ φ) : NDProof Γ (Formula.exists_ x φ)

  -- Existential Elimination
  | existsE {Γ x φ ψ}
      (h1 : NDProof Γ (Formula.exists_ x φ))
      (h2 : NDProof (φ :: Γ) ψ)
      (h_fresh : ¬ appears_free_in x (orList Γ)) : NDProof Γ ψ

  -- FOL Inference Rule (updated to use symbolic equivalence)
  | by_FOL {Γ φ} (h : FOL_entails_all Γ φ) : NDProof Γ φ

  --Diamond Intro Rule

  | diamond_intro {Γ : List Formula} {ℒ : List (String × Nat)} {φ : Formula}
    (h : NDProof Γ φ) 
    (h_closed : is_sentence φ []) : 
  NDProof Γ (Formula.diamond ℒ φ)

  --Diamond Elim Rule for 
| diamond_elim {Γ : List Formula} {ℒ : List (String × Nat)} {φ : Formula}
    (h1 : NDProof Γ (Formula.diamond ℒ φ))
    (h_equiv : FOL_equiv_all φ (restrict_formula_explicitly ℒ φ)) 
    (h_restricted : is_content_restricted_to ℒ (restrict_formula_explicitly ℒ φ)):
  NDProof Γ φ

 --Diamond Ignoring rule
| diamond_ignoring {Γ : List Formula}
    {ℒ ℒ' ℒ'' : List (String × Nat)} {φ : Formula}
    (h_diamond : NDProof Γ (Formula.diamond ℒ' φ))
    (h_sub : ℒ'.toFinset ⊆ ℒ.toFinset)  -- ℒ′ ⊆ ℒ
    (h_disjoint : Disjoint (ℒ''.map Prod.fst).toFinset (ℒ.map Prod.fst).toFinset)  -- ℒ″ ∩ ℒ = ∅
    (h_restricted : is_implicitly_content_restricted_to ℒ φ) :
  NDProof Γ (Formula.diamond (ℒ' ++ ℒ'') φ)

--simple comprehension
| simple_comprehension
    (R : String)
    (vars : List String)
    (Ψ : Formula)
    (φ : Formula)
    (body : Formula)
    (ℒ : List (String × Nat))
    (Γ : List Formula)
    (hΨ : NDProof Γ Ψ)
    (h_fresh_in_Ψ : ¬ mentions_relation R Ψ)
    (h_fresh_in_φ : ¬ mentions_relation R φ)
    (h_not_in_L : R ∉ ℒ.map Prod.fst)
    (h_eq : body = comprehension_body Ψ φ R vars)
    (h_closed : is_sentence body []) :
  NDProof Γ (Formula.diamond ℒ body)

--Relabeling 
| diamond_relabeling {Γ : List Formula} {ℒ : List (String × Nat)}
    {Θ Θ' : Formula}
    (h_proof : NDProof Γ (Formula.diamond ℒ Θ))
    (subst : List (String × String))
    (h_renamed : Θ' = Formula.rename_relations subst Θ)
    (h_disjoint_orig : ∀ r, r ∈ subst.map Prod.fst → r ∉ ℒ.map Prod.fst)
    (h_disjoint_new : ∀ r', r' ∈ subst.map Prod.snd → r' ∉ ℒ.map Prod.fst) :
  NDProof Γ (Formula.diamond ℒ Θ')

-- Importing 
| importing
      {Γ : List Formula} {ℒ : List (String × Nat)} {Θ Φ : Formula}
      (hΘ       : NDProof Γ Θ)
      (hDiamond : NDProof Γ (Formula.diamond ℒ Φ))
      (hCR      : is_implicitly_content_restricted_to ℒ Θ) :
    NDProof Γ (Formula.diamond ℒ (Formula.and Φ Θ))

--Logical Closure
| diamond_logical_closure
    {Γ : List Formula} {ℒ : List (String × Nat)} {Θ Φ : Formula}
    (h : NDProof Γ (Formula.diamond ℒ Θ))
    (h_entails : FOL_entails_all [Θ] Φ) :
  NDProof Γ (Formula.diamond ℒ Φ)

--Cutback

| cutback
    {Γ : List Formula}
    (ℒ : List (String × Nat))
    (P : String)
    {φ_exists φ_ext φ_forall : Formula}
    (h : NDProof Γ (Formula.and φ_exists φ_ext)) :
  NDProof Γ (Formula.diamond (ℒ ++ [(P, 1)]) φ_forall)

-- Modal Comprehension 

/--
Modal Comprehension:
If a formula φ is content-restricted to relations in ℒ ∪ {Q}, and does not mention R,
and Ψ is a sentence not mentioning R, then:

    From:  Γ ⊢ Ψ
    We can derive:
           Γ ⊢ ◇_{ℒ} (Ψ ⋀ □_{ℒ ∪ {R}} (∃!x̄. Q(x̄) → R(x̄) ⇔ φ))

This expresses the idea that:
It is logically possible (fixing ℒ) for R to apply **in such a way that**,
holding fixed the ℒ ∪ {R} structure, if Q selects a unique tuple x̄,
then R applies to x̄ iff φ holds (where φ is a modal sentence about how x̄ relates to the ℒ-structure).

In effect, this lets us **comprehend a fresh relation R** whose extension (possibly) matches
the extension of a complex modal property φ — even when φ includes nested modal operators —
without quantifying into modal contexts.

This rule generalizes ordinary comprehension principles from set theory by using conditional logical possibility
to simulate second-order quantification.

See the test case in ModalComprehensionTest for an example where this lets us say:
"it's logically possible that exactly those parents whose children are equinumerous with the wonders of the world are happy"
--/



| modal_comprehension 
    {Γ : List Formula} 
    {ℒ : List (String × Nat)} 
    {Ψ φ : Formula} 
    {R Q : String} 
    {n : Nat}
    (hΨ : NDProof Γ Ψ)
    (h_notin_Γ : ∀ γ ∈ Γ, ¬ mentions_relation R γ)
    (h_notin_φ : ¬ mentions_relation R φ)
    (h_notin_Ψ : ¬ mentions_relation R Ψ)
    (h_notin_ℒ : R ∉ ℒ.map Prod.fst)
    (h_sentence : is_sentence Ψ []) 
    (h_n_positive : n > 0)
    (h_phi_restricted : is_implicitly_content_restricted_to (ℒ ++ [(Q, n)]) φ) :
  NDProof Γ (modal_comprehension_formula ℒ Ψ φ R Q n)
-- Infinity 

| possible_infinity :
    NDProof [] (Formula.diamond [("S", 2)] infinity_axiom_body)

-- Possible Powerset
| possible_powerset
    (F C mem : String) :
  NDProof [] (Formula.diamond [(F,1), (C,1), (mem,2)] (possible_powerset_body F C mem)) 

-- Possible Choice
| possible_choice
    (L : List (String × Nat))
    (n m : Nat)
    (I R R_hat : String)
    (φ : Formula)
    (h_fresh_Rhat :
  R_hat ∉ (L ++ [(I, n), (R, n + m)]).map Prod.fst ∧
  R_hat ∉ collect_predicates φ) :
  NDProof [] (choice_axiom_modal L n m I R R_hat φ)

-- Possible amalgamation

  /--
    Amalgamation rule for possibility:

    If φ(x) is content-restricted to L ∪ Rs,
    then from the "index fix" premise:

      [] ⊢ □_L ( (∃!x (Q(x) ∧ I(x))) → ◇_{L,Q} (∀z (Q(z) → φ(z))) )

    we can infer:

      [] ⊢ amalgamation_axiom L I Rs R̂s φ extL

    (where extL defines the L-extension test.)
  --/
  | possible_amalgamation
      {Γ : List Formula} 
      (L     : List (String × Nat))
      (I Q     : String)
      (Rs    : List (String × Nat))
      (Rhats : List (String × Nat))
      (φ     : Formula)
      (h_index : NDProof  Γ (
         Formula.box L (
           Formula.imp
             (Formula.exists_unique "x" (
               Formula.and
                 (Formula.pred Q [Term.var "x"])  -- assuming Q is fixed in context
                 (Formula.pred I [Term.var "x"]))
             )
             (Formula.diamond (List.append L [(Q,1)]) (
               Formula.forall_ "z" (
                 Formula.imp
                   (Formula.pred Q [Term.var "z"]) 
                   (φ.substitute_var "x" "z")
               )
             ))
         )
      ))
      (hIinL    : (I,1) ∈ L)
      (hQfresh  : Q ∉ L.map Prod.fst)
      (hRsfresh : ∀ r ∈ Rs, r.fst ∉ L.map Prod.fst)
      (hRhatsfresh: ∀ r ∈ Rhats, r.fst ∉ L.map Prod.fst)
      (h_arities : ∀ i, i < Rs.length → (Rs.get! i).snd + 1 = (Rhats.get! i).snd)
      (h_content : is_implicitly_content_restricted_to (L ++ Rs) (
                   Formula.forall_ "x" (Formula.imp (Formula.pred I [Term.var "x"]) φ)
                 ))
    : NDProof Γ (Formula.amalgamation_axiom L I Rs Rhats φ)


notation Γ " ⊢" φ => NDProof Γ φ



--Example of using this rule
example :  [(Formula.and (Formula.pred "F" [Term.var "x"]) (Formula.pred "G" [Term.var "x"]))] ⊢ (Formula.pred "F" [Term.var "x"]) := by
apply NDProof.andE_left
apply NDProof.assumption
exact List.Mem.head _ 

-- Dummy test type
instance : Inhabited ℕ := ⟨0⟩


def test_formula : Formula :=
  Formula.exists_ "x"
    (Formula.and
      (Formula.pred "P" [Term.var "x"])
      (Formula.forall_ "y"
        (Formula.pred "R" [Term.var "x", Term.var "y"])))

def test_ℒ : List (String × Nat) := [("P", 1), ("R", 2)]

#eval restrict_formula_explicitly test_ℒ test_formula




@[simp] theorem map_pred_insertAt_range1 (r : String) (v : String) :
  List.map (fun j => Formula.pred r (insertAt [] j (Term.var v))) (List.range 1) = 
  [Formula.pred r [Term.var v]] := by
  simp [insertAt, List.range]
  rfl

@[simp] theorem orList_singleton (φ : Formula) :
  orList [φ] = φ := by
  simp [orList]


-- 1. For handling List.range 2
@[simp] theorem range_two :
  List.range 2 = [0, 1] := by rfl

-- 2. For List.map with simple functions
@[simp] theorem map_toString_range_one :
  List.map (fun i => "x" ++ toString i) (List.range 1) = ["x0"] := by
  simp [List.range, List.map]
  use 0
  constructor 
  dsimp [List.range.loop]
  rfl
  

  
  

-- 3. For handling List.reverse on short lists
@[simp] theorem reverse_singleton {α} (x : α) :
  [x].reverse = [x] := by rfl

-- 4. For mapping Term.var
@[simp] theorem map_term_var (vs : List String) :
  List.map Term.var vs = vs.map (fun v => Term.var v) := by rfl

-- 5. For specific insertAt cases with binary relations
@[simp] theorem insertAt_binary_rel_pos0 ( v₁ v₂ : String) :
  insertAt (List.map Term.var [v₁]) 0 (Term.var v₂) = 
  [Term.var v₂, Term.var v₁] := by
  unfold insertAt
  simp [List.splitAt]
  rfl

@[simp] theorem insertAt_binary_rel_pos1 (v₁ v₂  : String) :
  insertAt (List.map Term.var [v₁]) 1 (Term.var v₂ ) = 
  [Term.var v₁, Term.var v₂ ] := by
  unfold insertAt
  simp [List.splitAt]
  rfl

-- 6. For the specific use of List.foldl with existential quantifiers
@[simp] theorem foldl_exists_singleton (form : Formula) (v₁ : String):
  List.foldl (fun acc x => Formula.exists_ x acc) form [v₁ ] = 
  Formula.exists_ v₁  form := by
  simp [List.foldl]
  

-- 7. For orList with binary relations
 @[simp] theorem orList_binary_insertAt (r v₁ v₂ : String) :
  orList (List.map (fun j => Formula.pred r (insertAt [Term.var v₁] j (Term.var v₂))) [0, 1]) =
    Formula.or
      (Formula.pred r [Term.var v₂, Term.var v₁])
      (Formula.pred r [Term.var v₁, Term.var v₂]) := by
  unfold orList
  simp [insertAt_binary_rel_pos0, insertAt_binary_rel_pos1, List.map]

 
  
  

-- 8. For the nested foldl pattern
@[simp]
theorem foldl_exists_orList_binary (r v₁ v₂ : String) :
  List.foldl (fun acc x => Formula.exists_ x acc)
    (orList (List.map (fun j => Formula.pred r (insertAt [Term.var v₁] j (Term.var v₂))) [0, 1]))
    [v₁]
  =
  Formula.exists_ v₁ (
    Formula.or
      (Formula.pred r [Term.var v₂, Term.var v₁])
      (Formula.pred r [Term.var v₁, Term.var v₂])
  ) := by
  simp [insertAt, orList, List.map, List.foldl]



  -- For handling insertAt with Term.var directly (without List.map)
@[simp]
theorem insertAt_term_var_pos0 (v₁ v₂ : String) :
  insertAt [Term.var v₁] 0 (Term.var v₂) = 
    [Term.var v₂, Term.var v₁] := by
  simp [insertAt, List.take, List.drop]

@[simp]
theorem insertAt_term_var_pos1 (v₁ v₂ : String) :
  insertAt [Term.var v₁] 1 (Term.var v₂) = 
    [Term.var v₁, Term.var v₂] := by
  simp [insertAt, List.take, List.drop]


-- For predicates with insertAt terms
@[simp]
theorem pred_insertAt_pos0 (r v₁ v₂ : String) :
  Formula.pred r (insertAt [Term.var v₁] 0 (Term.var v₂)) =
    Formula.pred r [Term.var v₂, Term.var v₁] := by
  simp [insertAt]

@[simp]
theorem pred_insertAt_pos1 (r v₁ v₂ : String) :
  Formula.pred r (insertAt [Term.var v₁] 1 (Term.var v₂)) =
    Formula.pred r [Term.var v₁, Term.var v₂] := by
  simp [insertAt]

  
-- Basic constructors for lean
@[simp] theorem to_lean_prop_bot {σ : Type} [Inhabited σ]
  (P₀ : Formula → Prop) (P₁ : String → σ → Prop) (P₂ : String → σ → σ → Prop) (σ₁ : Assignment σ) :
  to_lean_prop P₀ P₁ P₂ σ₁ Formula.bot = False := by rfl

@[simp] theorem to_lean_prop_and {σ : Type} [Inhabited σ]
  (P₀ : Formula → Prop) (P₁ : String → σ → Prop) (P₂ : String → σ → σ → Prop)
  (σ₁ : Assignment σ) (φ ψ : Formula) :
  to_lean_prop P₀ P₁ P₂ σ₁ (Formula.and φ ψ) =
    (to_lean_prop P₀ P₁ P₂ σ₁ φ ∧ to_lean_prop P₀ P₁ P₂ σ₁ ψ) := by rfl

@[simp] theorem to_lean_prop_or {σ : Type} [Inhabited σ]
  (P₀ : Formula → Prop) (P₁ : String → σ → Prop) (P₂ : String → σ → σ → Prop)
  (σ₁ : Assignment σ) (φ ψ : Formula) :
  to_lean_prop P₀ P₁ P₂ σ₁ (Formula.or φ ψ) =
    (to_lean_prop P₀ P₁ P₂ σ₁ φ ∨ to_lean_prop P₀ P₁ P₂ σ₁ ψ) := by rfl

@[simp] theorem to_lean_prop_imp {σ : Type} [Inhabited σ]
  (P₀ : Formula → Prop) (P₁ : String → σ → Prop) (P₂ : String → σ → σ → Prop)
  (σ₁ : Assignment σ) (φ ψ : Formula) :
  to_lean_prop P₀ P₁ P₂ σ₁ (Formula.imp φ ψ) =
    (to_lean_prop P₀ P₁ P₂ σ₁ φ → to_lean_prop P₀ P₁ P₂ σ₁ ψ) := by rfl

@[simp] theorem to_lean_prop_not {σ : Type} [Inhabited σ]
  (P₀ : Formula → Prop) (P₁ : String → σ → Prop) (P₂ : String → σ → σ → Prop)
  (σ₁ : Assignment σ) (φ : Formula) :
  to_lean_prop P₀ P₁ P₂ σ₁ (Formula.neg φ) =
    ¬ to_lean_prop P₀ P₁ P₂ σ₁ φ := by rfl


-- Quantifiers
@[simp] theorem to_lean_prop_forall {σ : Type} [Inhabited σ]
  (P₀ : Formula → Prop) (P₁ : String → σ → Prop) (P₂ : String → σ → σ → Prop)
  (σ₁ : Assignment σ) (x : String) (φ : Formula) :
  to_lean_prop P₀ P₁ P₂ σ₁ (Formula.forall_ x φ) =
    (∀ (u : σ), to_lean_prop P₀ P₁ P₂ (Function.update σ₁ x u) φ) := by rfl

@[simp] theorem to_lean_prop_exists {σ : Type} [Inhabited σ]
  (P₀ : Formula → Prop) (P₁ : String → σ → Prop) (P₂ : String → σ → σ → Prop)
  (σ₁ : Assignment σ) (x : String) (φ : Formula) :
  to_lean_prop P₀ P₁ P₂ σ₁ (Formula.exists_ x φ) =
    (∃ (u : σ), to_lean_prop P₀ P₁ P₂ (Function.update σ₁ x u) φ) := by rfl

-- Predicates
@[simp] theorem to_lean_prop_pred_unary {σ : Type} [Inhabited σ]
  (P₀ : Formula → Prop) (P₁ : String → σ → Prop) (P₂ : String → σ → σ → Prop)
  (σ₁ : Assignment σ) (r x : String) :
  to_lean_prop P₀ P₁ P₂ σ₁ (Formula.pred r [Term.var x]) =
    P₁ r (σ₁ x) := by rfl

@[simp] theorem to_lean_prop_pred_binary {σ : Type} [Inhabited σ]
  (P₀ : Formula → Prop) (P₁ : String → σ → Prop) (P₂ : String → σ → σ → Prop)
  (σ₁ : Assignment σ) (r x y : String) :
  to_lean_prop P₀ P₁ P₂ σ₁ (Formula.pred r [Term.var x, Term.var y]) =
    P₂ r (σ₁ x) (σ₁ y) := by rfl


  

def test_formula_2 : Formula :=
  Formula.exists_ "x"
    (Formula.and
      (Formula.pred "P" [Term.var "x"])
      (Formula.forall_ "y"
        (Formula.imp
          (Formula.pred "R" [Term.var "x", Term.var "y"])
          (Formula.pred "R" [Term.var "y", Term.var "x"]))))


--Amalgamation Test

namespace AmalgamationTest

-- Background structure
abbrev L : List (String × Nat) := [("parent", 2), ("I", 1)]

-- Index predicate and fresh marker
abbrev I_name := "I"
abbrev Q_name := "Q"

-- Original and slice‑relations
abbrev Rs   : List (String × Nat) := [("ghost", 1)]
abbrev Rhats : List (String × Nat) := [("ghost_slice", 2)]

-- The one‑place formula φ(x) talking about the original relation
abbrev φ : Formula := Formula.pred "ghost" [Term.var "x"]

-- The index‑fix premise:
abbrev index_fix : Formula :=
  Formula.box L (
    Formula.imp
      (Formula.exists_unique "x" (
        Formula.and
          (Formula.pred Q_name [Term.var "x"])
          (Formula.pred I_name [Term.var "x"]))
      )
      (Formula.diamond (L ++ [(Q_name,1)]) (
        Formula.forall_ "z" (
          Formula.imp
            (Formula.pred Q_name [Term.var "z"])
            (φ.substitute_var "x" "z")
        )
      ))
  )

#eval index_fix

-- Test: from the index_fix premise, derive the general amalgamation axiom
example : [index_fix] ⊢ Formula.amalgamation_axiom L I_name Rs Rhats φ := by
  -- bring the premise into scope
  have h_index : [index_fix] ⊢ index_fix := by apply NDProof.assumption; apply List.Mem.head
  -- apply the Amalgamation rule
  -- 
  dsimp[index_fix, Formula.amalgamation_axiom, L, I_name, Rs, Rhats, φ]
  simp 
  apply NDProof.possible_amalgamation [("parent", 2), ("I", 1)] 
  simp 
  dsimp[index_fix, Formula.amalgamation_axiom, L, I_name, Rs, Rhats, φ] at h_index
  exact h_index
  simp 
  simp 
  dsimp [Q_name]
  constructor 
  simp 
  simp 
  simp 
  intro x
  intro h_x 
  simp at h_x
  rw [h_x]
  simp 
  intros x 
  simp 
  intro h 
  rw [h]
  simp 
  dsimp [is_content_restricted_to]
  simp 
  dsimp [FOL_equiv_all]
  simp 
  constructor 
  intro σ 
  intros 
  constructor 
  intro h
  intro σ'
  intro h2
  exact h σ'
  intro h2
  intro y
  have h3 := h2 y
  intro h4
  apply h3
  right 
  left
  exact h4
  exact h4
  rfl  

 



  -- discharge side‑conditions
  all_goals simp [L, Rs, Rhats, I_name, Q_name]

end AmalgamationTest



--Possible choice test

namespace ChoiceTest

def dummy_phi : Formula := Formula.exists_ "x" (Formula.pred "Z" [Term.var "x"]) -- stand-in for φ

def goal : Formula :=
  choice_axiom_modal [("L0", 1)] 1 1 "I" "R" "R̂" dummy_phi

example : [] ⊢ goal := by
  apply NDProof.possible_choice [("L0", 1)] 1 1 "I" "R" "R̂" dummy_phi 
  dsimp[collect_predicates, dummy_phi]
  simp

#eval goal

end ChoiceTest

-- Possible Powerset Test 

namespace PowersetTest

def powerset_goal : Formula :=
  Formula.diamond [("F", 1), ("C", 1), ("mem", 2)] (possible_powerset_body "F" "C" "mem")

example : [] ⊢ powerset_goal := by
  apply NDProof.possible_powerset "F" "C" "mem"
end PowersetTest

-- Infinity test

namespace InfinityTest

example : [] ⊢ infinity_axiom_modal := by
  dsimp [infinity_axiom_modal,  infinity_axiom_body,     infinity_clause_1,
    infinity_clause_2,
    infinity_clause_3,
    infinity_clause_4,
    infinity_clause_5]
  apply NDProof.possible_infinity
end InfinityTest


--Modal Comprehension test

namespace ModalComprehensionTest

/--
This test illustrates the motivation for the modal comprehension rule, inspired by the idea that:
  "It could be (holding fixed the facts about parenthood and being a wonder of the world) that exactly those parents whose children are equinumerous with the wonders of the world are happy."

To formalize this, we express a comprehensionlike idea that a fresh property `happy` could apply in a way that's coextensive with a modal property — having children equinumerous with the wonders.
     *We can start to express this modal property using conditional logical possibility and a fresh relation `points_at` -- by saying that x's children are equinumerous with the wonders iff it's possible holding fixed the extension of `child of` that for all x if x is a parent (i.e. x has at least one child) then it's possible (holding fixed the application of parent of) for that `points at` bijects x's children with the wornders of the world.  
     *This gives us a possibility claim that involves quantifying in ◇_{parent_of, wonder} (∀ x) [Happy(x) iff (∃ y) parent_of(x,y) & ◇_{parent_of, wonder} `points at' bijects the children of x with the wonders of the world].
     *But quantifying in is not allowed in our language! 
     *Luckily we can modify this biconditional to express the same idea without quantifying into modal contexts by a using the following trick. We replace claims about what's true for all objects x in the L structure.. with claims about what's necessary for logically possible (holding fixed the L structure) way fresh predicate Q  could select a unique position in the L structure, and talk about what is possible/necessary fixing this choice of a position for Q.
     *So, Rather than describing a scenario where happiness applies to those individuals with children equinumerous with the wonders by saying 
              (old)  for all x, x is happy iff x is in the L structure and Diamond_{L} phi(x),
               we say 
              (ii) it's logically necessary (given how all relations in the L and happiness applies) that if Q selects a unique object x in the L structure then that selected object x is happy iff [Diamond_{L,Q} for all x, if Q(x) then phi(x) ] (i.e. if it is possible (fixing the L and Q strucuture, hence the unique position within the L structure selected by Q) that the thing in the unique position selected by Q has phi) 

So the intended structure of the formula is:

◇_{parent, wonder}
 □_{parent, wonder, happy}
  (∃!x. Q(x)) →
   (happy(x) ⇔
    ◇_{parent, wonder, Q} [if Q(x) then x’s children are bijected with the wonders by `points at'])

NOTE TO SELF: Check (a) how to explain the modal comprehension intuition in this example and the wrapping trick well (b) whether I can write a test that corresponds to it (see if the test below is missing something) (c) make sure my comprehension rule (as stated in the book or in the clause above, or in some polished way I will think of now, states a general principle that implies this specific case and which I think is clearly true)

--/



def φ : Formula :=
  ◇_{[("parent", 2), ("wonder", 1), ("Q", 1)]} (
    A"x", Formula.imp 
      (Formula.pred "Q" [Term.var "x"])
      (
        Formula.and
          (A"y", A"z", A"w", 
            Formula.imp 
              (Formula.and (Formula.and (Formula.pred "child" [Term.var "x", Term.var "y"]) 
                                         (Formula.pred "child" [Term.var "x", Term.var "z"]))
                           (Formula.and (Formula.pred "points_at" [Term.var "y", Term.var "w"])
                                        (Formula.pred "points_at" [Term.var "z", Term.var "w"])))
              (Formula.eq (Term.var "y") (Term.var "z"))
          )
          (A"w", Formula.imp (Formula.pred "wonder" [Term.var "w"])
                             (E"y", Formula.and 
                                (Formula.pred "child" [Term.var "x", Term.var "y"])
                                (Formula.pred "points_at" [Term.var "y", Term.var "w"])
                             ))
      )
  )

-- Ψ says: Q picks out a unique object.
def Ψ : Formula := Formula.exists_unique_many "Q" 1

-- We define the outer modal context
def ℒ : List (String × Nat) := [("parent", 2), ("wonder", 1)]
def R' : String := "happy"
def Q' : String := "Q"
def n : Nat := 1

-- Define φ as a sentence content restricted to ℒ ++ [Q]
def φ'' : Formula := ◇_{ℒ ++ [(Q', n)]} (
                      Formula.forall_many ["x"] (
                        Formula.pred Q' [Term.var "x"] ⇒
                        ◇_{ℒ} (
                          Formula.exists_ "x" (Formula.pred "points_at" [Term.var "x", Term.var "x"])
                        )
                      )
                   )

-- Use the helper function for generating the correct goal
def goal : Formula := modal_comprehension_formula ℒ Ψ φ'' R' Q' n

example : [Ψ] ⊢ goal := by
  dsimp [goal, Ψ, φ'', ℒ, R', Q', n]
  have h : [Ψ] ⊢ Ψ := by
    apply NDProof.assumption
    apply List.Mem.head
  dsimp [Ψ, Formula.exists_unique_many, ] at h
  simp at h
  simp 
  apply NDProof.modal_comprehension
  ·  exact h 
  · simp
    dsimp[Formula.forall_many, Formula.exists_many] 
    simp
  · dsimp[Formula.forall_many, Formula.exists_many]
    simp 
  · dsimp [Formula.forall_many]
    simp  
  · dsimp [is_sentence, Formula.forall_many]
    simp 
  · dsimp [is_sentence, Formula.forall_many]
    simp 
  · dsimp [FOL_equiv_all] 
    simp 
  dsimp[is_implicitly_content_restricted_to, FOL_equiv_all]
  intros 
  constructor 
  intros
  dsimp [to_lean_prop, restrict_formula_explicitly_core,Formula.forall_many ]
  rfl
  simp 
  dsimp [Formula.forall_many ,restrict_formula_explicitly_core]
  simp 
  

    
    

end ModalComprehensionTest

namespace SiblingsModalComprehensionTest

-- This file encodes the “Siblings” motivating example for Modal Comprehension (Axiom 8.9 in the book).
-- See Chapter 8.8 (pp. 95–97) of the LFPS text: the informal “Siblings” example appears just above Axiom 8.9.
-- Here we formally instantiate that axiom to define a fresh predicate `Happy`:
--   * L = ["Married",2; "Sibling",2]
--   * Ψ asserts the background world has at least one sibling pair
--   * Q is a fresh unary choice predicate (∃!x, Q x)
--   * φ says: possibly (fixing Married,Sibling,Q) that the chosen x has more siblings than each of its spouses,
--     witnessed by a non-injective surjection `Z` between sibling sets.
-- The final `InstConclusion` is exactly the head of the sequent one gets by applying Modal Comprehension:
--   from `Γ ⊢ Ψ` infer `Γ ⊢ InstConclusion`.

-- Background structure: Married and Sibling are binary relations
abbrev L : List (String × Nat) := [("Married", 2), ("Sibling", 2)]

-- Fresh relation for comprehension and its arity
def R' : String := "R"
def Q': String := "Q"
def n : Nat := 1  -- Q is unary

-- Ψ asserts Q picks out a unique individual
def Ψ : Formula := Formula.exists_unique_many Q' n

-- We formalize “x has more siblings than their spouse” by positing a relation Z
--   from siblings of x onto siblings of y that is surjective but not injective.
def MapR : String := "Z"

-- The mapOK formula:
def mapOK (x y : String) : Formula :=
  -- 1. Z maps between the correct sets of siblings
  Formula.forall_many ["u","v"] (
    Formula.imp
      (Formula.pred MapR [Term.var "u", Term.var "v"])
      (Formula.and
        (Formula.pred "Sibling" [Term.var x, Term.var "u"])
        (Formula.pred "Sibling" [Term.var y, Term.var "v"]))
  ) ⋀
  -- 2. Surjectivity onto siblings of y: every sibling of y has a preimage
  Formula.forall_ "u" (
    Formula.imp
      (Formula.pred "Sibling" [Term.var y, Term.var "u"])
      (Formula.exists_ "u'" (Formula.pred MapR [Term.var "u'", Term.var "u"]))
  ) ⋀
  -- 3. Non-injectivity: some v has two distinct preimages in siblings of x
  Formula.exists_many ["u1","u2","v"] (
  Formula.and
    (Formula.and
      (Formula.pred MapR [Term.var "u1", Term.var "v"])
      (Formula.pred MapR [Term.var "u2", Term.var "v"]))
    (Formula.neg (Formula.eq (Term.var "u1") (Term.var "u2")))
)

-- φ says: it is possible (fixing L and Q) that for the unique x selected by Q,
-- for every y that x is married to (allowing multiple spouses), mapOK(x,y) obtains.

def φ : Formula :=
  Formula.diamond (L ++ [(Q', n)]) (
    Formula.forall_ "x" (
      Formula.imp (Formula.pred Q' [Term.var "x"]) (
        Formula.forall_ "y" (
          Formula.imp
            (Formula.pred "Married" [Term.var "x", Term.var "y"])
            (mapOK "x" "y")
        )
      )
    )
  )

-- ψ could be any sentence; here: “there is at least one sibling pair”
def ψ : Formula :=
  Formula.exists_ "x" (Formula.exists_ "y" (Formula.pred "Sibling" [Term.var "x", Term.var "y"]))


abbrev InstConclusion : Formula :=
  -- ◇_{L} ( Ψ ⋀ □_{L ∪ {Happy}} [ (∃! x, Q x) → (∃! x, Q x ⋀ (Happy x ↔ (Ext L x ⋀ φ))) ] )
  Formula.diamond L
    ( Formula.and Ψ
      ( Formula.box (L ++ [("Happy", 1)])
        ( Formula.imp
          (Formula.exists_unique_many Q' n)  -- first arg to `imp`
          ( Formula.and
            (Formula.pred Q' [Term.var "x"])  -- second arg to `imp`
            ( Formula.iff
              (Formula.pred "Happy" [Term.var "x"])
              ( Formula.and
                (Ext L "x")
                φ
              )
            )
          )
        )
      )
    )


-- Now we test that [ Ψ ] ⊢  ◇_{L} ( Ψ ⋀ □_{L ∪ {Happy}} [ (∃! x, Q x) → (∃! x, Q x ⋀ (Happy x ↔ (Ext L x ⋀ φ))) ] )
example : [Ψ] ⊢ InstConclusion := by
  -- … here you would apply `NDProof.modal_comprehension` to `φ` and `Ψ` …
  admit

end SiblingsModalComprehensionTest

-- Cutback Test

namespace CutbackTest

def ℒ : List (String × Nat) := [("R", 1)]

def φ_exists : Formula := Formula.exists_ "x" (Formula.pred "P" [Term.var "x"])
def φ_ext : Formula :=
  Formula.forall_ "x" (Formula.imp (Ext ℒ "x") (Formula.pred "P" [Term.var "x"]))
def φ_forall : Formula := Formula.forall_ "x" (Formula.pred "P" [Term.var "x"])

def φ : Formula := Formula.and φ_exists φ_ext
def goal : Formula := Formula.diamond (ℒ ++ [("P", 1)]) φ_forall

example : [φ] ⊢ goal := by
have h : [φ] ⊢ φ := by 
  apply NDProof.assumption
  apply List.Mem.head
dsimp [φ] at h 
dsimp [φ_ext,  φ_exists, ℒ] at h
simp at h 
dsimp [φ, goal, ℒ, φ_exists, φ_ext, φ_forall]
simp 
apply NDProof.cutback  [("R", 1)] "P" h



end CutbackTest

--Logical Closure test

namespace LogicalClosureTest

def ℒ : List (String × Nat) := [("R", 1)]

-- Modal premise ◇_ℒ (∃y. R(y))
def Θ : Formula := Formula.exists_ "y" (Formula.pred "R" [Term.var "y"])
def Φ : Formula := Formula.exists_ "z" (Formula.pred "R" [Term.var "z"])

def premise : Formula := Formula.diamond ℒ Θ
def goal : Formula := Formula.diamond ℒ Φ

example : [premise] ⊢ goal := by
dsimp [premise,goal]
have h: [Θ] ⊢ Φ := by
  dsimp  [Θ,Φ]
  apply NDProof.by_FOL
  dsimp [to_lean_prop] 
  simp
have prem: [premise] ⊢ premise := by
  apply NDProof.assumption
  simp   
apply NDProof.diamond_logical_closure prem 
simp
dsimp [Θ,Φ]
simp


  -- You’ll implement this using NDProof.diamond_logical_closure
  -- With a by_FOL step showing ∃y R(y) ⊢ ∃z R(z)

end LogicalClosureTest

-- Importing 
namespace ImportingTest




def ℒ : List (String × Nat) := [("R", 1)]

--something Θ implicitly content restricted to L that we will want to import into a Diamond_{L} context to get  Diamond_{L} ( Φ &  Θ)

def Θ   : Formula :=
  Formula.exists_ "y" (Formula.pred "R" [Term.var "y"])

def  Φ : Formula :=
  E"x", Formula.pred "F" [Term.var "x"] ⋀ Formula.pred "G" [Term.var "x"]
  




example : [Θ, Formula.diamond ℒ Φ] ⊢ Formula.diamond ℒ (Formula.and Φ Θ) := by
  have h1 : ([Θ, Formula.diamond ℒ Φ] ⊢ Θ) := by
    apply NDProof.assumption
    apply List.Mem.head
  have h2 : [Θ, Formula.diamond ℒ Φ] ⊢ Formula.diamond ℒ Φ := by
    apply NDProof.assumption
    apply List.Mem.tail 
    apply List.Mem.head
  apply NDProof.importing
  exact h1 
  exact h2
  dsimp [Θ, ℒ, Φ]
  dsimp [FOL_equiv_all]
  simp 
  rfl





end ImportingTest
--Relabeling proof test

def Θ : Formula :=
  E"x", Formula.pred "F" [Term.var "x"] ⋀ Formula.pred "G" [Term.var "x"]

def Θ' : Formula :=
  E"x", Formula.pred "P" [Term.var "x"] ⋀ Formula.pred "Q" [Term.var "x"]

def oldRels : List (String × Nat) := [("F", 1), ("G", 1)]
def newRels : List (String × Nat) := [("P", 1), ("Q", 1)]

def modal_context : List (String × Nat) := [("R", 2)]

def prem : Formula := ◇_{modal_context} Θ
def goal : Formula := ◇_{modal_context} Θ'

example : [prem] ⊢ goal := by
dsimp [prem, goal, modal_context, Θ, Θ']
have h: [◇_{[("R", 2)]}
      E"x",
        Formula.pred "F" [Term.var "x"] ⋀
          Formula.pred "G"
            [Term.var "x"]]  ⊢ ◇_{[("R", 2)]}
      E"x",
        Formula.pred "F" [Term.var "x"] ⋀
          Formula.pred "G"
            [Term.var "x"] 
apply NDProof.assumption
apply List.Mem.head
let subst := [("F","P"), ("G", "Q")]
apply  NDProof.diamond_relabeling h [("F","P"), ("G", "Q")]
simp 
dsimp
simp 
dsimp
simp  



---Comprehension Proof Test
section ComprehensionTest

def Ψ' : Formula := Formula.forall_ "y" (Formula.pred "Q" [Term.var "y"])

def φ' : Formula := Formula.neg (Formula.pred "P" [Term.var "z", Term.var "w"])

def ℒ : List (String × Nat) := [("Z", 3)]

def R' : String := "R"

def vars : List String := ["z", "w"]

-- test1 uses forall_many
def test1 : Formula := Formula.forall_many ["x", "y"] (Formula.pred "R" [Term.var "x", Term.var "y"])

-- test2 builds the same structure manually
def test2 : Formula := Formula.forall_ "x" (Formula.forall_ "y" (Formula.pred "R" [Term.var "x", Term.var "y"]))

#eval is_sentence test1 []   -- should be true
#eval is_sentence test2 []   -- should be true
#eval test1 == test2         -- should be true

def comprehension_goal : Formula :=
  Formula.diamond ℒ (
    Formula.and Ψ' (
      Formula.forall_many vars (
        Formula.iff
          (Formula.pred R' (vars.map Term.var))
          φ')))

#eval comprehension_goal

def comprehension_goal_manual : Formula :=
  Formula.diamond ℒ (
    Formula.and Ψ' (
      Formula.forall_ "z" (
        Formula.forall_ "w" (
          Formula.iff
            (Formula.pred "R" [Term.var "z", Term.var "w"])
            φ'))))

example : [Ψ'] ⊢ comprehension_goal := by
dsimp [comprehension_goal,Ψ',ℒ,φ',R', vars]
have h:  [Ψ'] ⊢ Ψ'
apply NDProof.assumption
apply List.Mem.head
dsimp [Ψ'] at h
dsimp [Formula.forall_many]
let Ψ := Formula.forall_ "y" (Formula.pred "Q" [Term.var "y"])
let φ := Formula.neg (Formula.pred "P" [Term.var "z", Term.var "w"])
apply NDProof.simple_comprehension  "R" ["z","w"] Ψ φ
apply NDProof.assumption
apply List.Mem.head
simp [Ψ]
simp [φ]
dsimp [comprehension_body]
simp  
dsimp [comprehension_body]
simp [Ψ,φ, Formula.forall_many]
simp 







example : [Ψ'] ⊢ comprehension_goal_manual := by
dsimp [comprehension_goal_manual,Ψ',ℒ,φ',R', vars]
have h:  [Ψ'] ⊢ Ψ'
apply NDProof.assumption
apply List.Mem.head
dsimp [Ψ'] at h
let Ψ := Formula.forall_ "y" (Formula.pred "Q" [Term.var "y"])
let φ := Formula.neg (Formula.pred "P" [Term.var "z", Term.var "w"])
apply NDProof.simple_comprehension  "R" ["z","w"] Ψ φ
apply NDProof.assumption
apply List.Mem.head
simp [Ψ]
simp [φ]
dsimp [comprehension_body]
simp  
dsimp [comprehension_body]
simp [Ψ,φ, Formula.forall_many]
simp 


end ComprehensionTest

def φ := Formula.exists_ "x" (Formula.pred "P" [Term.var "x"])
def modal_φ := Formula.diamond [("P", 1), ("R", 2)] φ
def modal_φ' := Formula.diamond [("P", 1)] φ

--Diamond Weakening Goal 

example: [modal_φ']  ⊢ modal_φ := by 
dsimp [modal_φ, modal_φ']
have h : [modal_φ']  ⊢ modal_φ' 
apply NDProof.assumption
apply List.Mem.head
dsimp [modal_φ, modal_φ'] at h
have h': [("P", 1)].toFinset ⊆ [("P", 1)].toFinset
simp
refine NDProof.diamond_ignoring h h' ?_ ?_
simp
simp 
dsimp [FOL_equiv_all]
constructor
intros 
dsimp [φ] 
simp 
dsimp [φ] 
simp 
rfl






--Diamond E goal

example : [modal_φ] ⊢ φ := by
dsimp [modal_φ, φ]
apply NDProof.diamond_elim
apply NDProof.assumption
exact List.Mem.head _
dsimp [FOL_equiv_all]
intros
simp 
constructor 
intro h
rcases h with ⟨x,hx⟩
use x
constructor
left
exact hx
exact hx
intro h
rcases h with ⟨x,hx⟩
use x
exact hx.right
simp 
rfl
-- Equivalence goal



example : FOL_equiv_all test_formula_2 (restrict_formula_explicitly test_ℒ test_formula_2) := by
  dsimp [FOL_equiv_all]
  intros 
  dsimp [test_formula_2]
  dsimp [test_ℒ]
  simp 
  constructor
  intros h
  rcases h with ⟨x,hx⟩
  use x
  constructor
  left
  exact hx.left
  constructor 
  exact hx.left
  intro y
  intro hy
  intro hy'
  have hxy:= hx.right y
  exact hxy hy'
  intro h 
  rcases h with ⟨x,hx⟩
  use x
  have hright := hx.right
  constructor 
  exact hright.left
  intro y
  intro hante
  have h3:= hright.right
  have h4:= h3 y
  apply h4
  right
  use x 
  right
  exact hante
  tauto







section semantics

  
  universe u'
  variable {α : Type u'} [Inhabited α]
  
  /-- A world has
    • a `domain : α → Prop` (which elements exist here),
    • an `interp : String → List α → Prop`. -/
  structure World (α : Type u') where
    domain : α → Prop
    interp : String → List α → Prop
    default     : α
    default_mem : domain default
/-- A plain valuation, no subtypes. -/
abbrev Val (w : World α) := String → α
  
  /-- The extension of a list of relation‐names `Rs` in world `w` is the set
      of all elements that appear in any tuple that `w.interp r ts` holds of. -/
  def worldExt {α : Type u'} (w : World α) (Rs : List String) : Set α :=
    { a |
      ∃ (r : String) (ts : List α),
        r ∈ Rs ∧               -- now this is just a conjunction
        w.interp r ts ∧
        a ∈ ts
    }

/--  f : α → α  is a bijection *from*  S  *onto*  S'  —  
    i.e.   f[S] = S'   and   f|S  is injective  -/
structure BijOn (f : α → α) (S S' : Set α) : Prop where
  inj : ∀ ⦃x y⦄, x ∈ S → y ∈ S → f x = f y → x = y
  sur : ∀ y ∈ S', ∃ x ∈ S, f x = y


/-- M' is L‐accessible from M iff there is a bijection 
    f : worldExt M Rs   ≃   worldExt M' Rs
    which moreover *respects* each frozen relation in Rs. -/
def accessible (L : List (String × ℕ)) (M M' : World α) : Prop :=
  let Rs := L.map Prod.fst;  
  ∃ (f : α → α),
    BijOn f (worldExt M Rs) (worldExt M' Rs) ∧
    ∀ (r : String) (ts : List α),
      r ∈ Rs →
      (∀ a ∈ ts, a ∈ worldExt M Rs) →
      (M.interp r ts ↔ M'.interp r (ts.map f))


/-- Now our Kripke‐style diamond looks for any *isomorphic* L‐world. -/
def eval (w : World α) (v : Val w) : Formula → Prop
  | Formula.bot        => False
  | Formula.var _      => False  -- if you’re not using propositional atoms, just `False`
  | Formula.iff φ ψ    => (eval w v φ) ↔ (eval w v ψ)
  | Formula.pred r as  =>
    let ts := as.map (fun t => match t with
      | Term.var x => v x
      | _          => default )
    -- require every ts in the domain, then check the relation
    (∀ a ∈ ts, w.domain a) ∧ w.interp r ts

  | Formula.eq t₁ t₂   =>
    match t₁, t₂ with
    | Term.var x, Term.var y => v x = v y
    | _, _                   => False

  | Formula.and φ ψ     => eval w v φ ∧ eval w v ψ
  | Formula.or  φ ψ     => eval w v φ ∨ eval w v ψ
  | Formula.imp φ ψ     => eval w v φ → eval w v ψ
  | Formula.neg φ       => ¬ eval w v φ

  | Formula.forall_ x φ =>
    -- only range over actual-domain elements
    ∀ (a : α), w.domain a →
      eval w (fun y => if y = x then a else v y) φ

  | Formula.exists_ x φ =>
    ∃ (a : α), w.domain a ∧
      eval w (fun y => if y = x then a else v y) φ

  | Formula.diamond Rs φ =>
    -- look for any L‐accessible isomorphic world w' and reuse the composite f ∘ v
    ∃ (w' : World α) (f : α → α),
      accessible Rs w w' ∧
      -- `accessible` should already bundle in: ∀ a, w.domain a → w'.domain (f a)
      eval w' (f ∘ v) φ

  | Formula.box Rs φ =>
    ∀ (w' : World α) (f : α → α),
      accessible Rs w w' → 
      eval w' (f ∘ v) φ

/-- Finally, truth in `w` means “holds under some default valuation” -we consider the valuation that assigns everything to the default object, but we only ever need this for sentences with
   no free variables. -/
def TrueIn (w : World α) (φ : Formula) : Prop :=
  -- send every variable to the one “default” a ∈ w.domain
  eval w (fun _ => w.default) φ
  

  
  
end semantics 


 
 
  







 


   
  

