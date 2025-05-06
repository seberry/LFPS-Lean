

## **🧭 1\. Defining the Language of Logical Possibility and the Proof System**

I've developed a formal language tailored to express logical possibility, accompanied by a natural deduction proof system. This system is encapsulated in the inductive type `NDProof`, which represents derivations of the form `Γ ⊢ φ`—indicating that the formula `φ` is provable from the set of assumptions `Γ`.

Each inference rule from the book is mirrored by a constructor in `NDProof`. For instance, the diamond elimination rule corresponds to `NDProof.diamond_elim`. This alignment ensures that the formal system in Lean faithfully represents the logical framework presented in the book.

---

## **📐 2\. Confirming Content Restriction**

An unusual feature of the system defined in the book is that the applicability of many proof rules — especially modal rules like Diamond Elimination — depends on whether the sentence in question is **content-restricted** to a given list of predicates or relations. That is: we can only infer `φ` from `◇_{P,R} φ` if the truth of `φ` is determined *solely* by the extensions of `P` and `R`.

This idea is formally defined in Chapter 7, where we say a formula is content-restricted to `P, R` if it only quantifies over things that are “tied into” the P/R structure — roughly, things satisfying `Ext(P, R)`, as defined there.

To make this checkable in Lean, the proof checker requires a *reduction to first-order logic*. Specifically, whenever you apply a rule that requires content restriction, you must:

1. **Prove that your sentence φ is first-order logically equivalent** to a formula φ′ that is explicitly content-restricted to the appropriate symbols.

2. The checker **automatically generates** one such φ′ using a syntactic transformation that inserts restriction clauses — essentially ensuring that all quantifiers only range over “connected” objects.

3. You then prove that `φ ↔ φ′` in Lean — thereby showing that φ is implicitly content-restricted.

For example, to prove that `∃x P(x)` is implicitly content-restricted to `P` and `R`, the system auto-generates the sentence:

```
∃x, ((P(x) ∨ ∃y (R(x,y) ∨ R(y,x))) ∧ P(x))
```

and asks you to prove:

```
∃x P(x) ↔ ∃x ((P(x) ∨ ∃y (R(x,y) ∨ R(y,x))) ∧ P(x))
```

This ensures that all relevant objects are “tied into” the P/R structure, and that no extra-world structure can influence the truth of `φ`.

In Lean, this is internalized using a goal like:

```
∀ P₁ P₂, (∃x, P₁ "P" x) ↔ ∃x, ((P₁ "P" x ∨ ∃y, P₂ "R" x y ∨ P₂ "R" y x) ∧ P₁ "P" x)
```

Here, `P₁` and `P₂` are assignments of predicate and relation names (like `"P"` and `"R"`) to actual Lean predicates. The universal quantification ensures you're showing this equivalence holds for **all interpretations** — just as in the model-theoretic account from the book.

By proving this equivalence, you show that `∃x P(x)` is implicitly content-restricted to `{P, R}` — and thus qualifies for modal elimination in the formal system.

---

## **🧰 3\. Leveraging Lean's Native FOL Reasoning**

Lean's robust support for first-order logic allows us to perform these equivalence proofs effectively. By translating our custom formulas into Lean's native propositions, we can utilize its suite of tactics to establish logical equivalences.

For example, to prove that `∃x P(x)` is equivalent to its content-restricted counterpart, we can use tactics like `intros`, `use`, and `exact` to construct the necessary proof steps. This integration ensures that our system benefits from Lean's powerful reasoning capabilities while maintaining the integrity of our custom logic.

---

## **🧪 4\. Annotated Example: Applying Diamond Elimination**

Let's consider a simple proof:

```
def φ := Formula.exists_ "x" (Formula.pred "P" [Term.var "x"])
def modal_φ := Formula.diamond [("P", 1), ("R", 2)] φ

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
  rcases h with ⟨x, hx⟩
  use x
  constructor
  left
  exact hx
  exact hx
  intro h
  rcases h with ⟨x, hx⟩
  use x
  exact hx.right
  simp
  rfl
```

**Explanation:**

1. **Definitions**:

   * `φ` is defined as `∃x P(x)`.

   * `modal_φ` represents `◇_{P,R} φ`, indicating that `φ` is possibly true, considering only the interpretations of `P` and `R`.

2. **Proof Steps**:

   * `dsimp [modal_φ, φ]`: Simplifies the definitions to expose the underlying structure.

   * `apply NDProof.diamond_elim`: Applies the diamond elimination rule, which requires that `φ` is content-restricted to `P` and `R`.

   * `apply NDProof.assumption` and `exact List.Mem.head _`: Justifies that `modal_φ` is among our assumptions.

   * `dsimp [FOL_equiv_all]`: Unfolds the definition of first-order logical equivalence.

   * The subsequent steps construct a proof that `φ` is logically equivalent to a formula explicitly content-restricted to `P` and `R`.  

   **📌**  **Why the scary goal?**  
      The proof checker is now verifying that `∃x P(x)` is implicitly content-restricted to `P, R`, as required to apply `diamond_elim`. That means proving it’s logically equivalent to a syntactically restricted formula (where all quantifiers range over “P or R related” objects). See Chapter 7 of the book and the [content restriction section](https://chatgpt.com/g/g-p-680481eb59188191ae26fd73b6a10885-lean-proof-checker-for-lfp-modal-logic/c/docs/content-restriction.md) for more on this.

## 💡**5\. Why Lean?**

This project is implemented in [Lean 4](https://leanprover.github.io/) because of its strong support for formalizing and verifying logical systems.

Long-term, Lean is also being used for exciting research in AI-assisted formal reasoning. I'm hoping to eventually translate the long proofs in the appendix of the book (which show that every FOL theorem of ZFC has a potentialist translation derivable in this system) into Lean-checked proofs — allowing full verification from axioms and definitions alone.

### **🎮 Want to try Lean?**

If you're new to Lean, I recommend the [Natural Number Game](https://adam.math.hhu.de/lean-game) — a hands-on, puzzle-based way to learn the basics. It’s how I got started.

