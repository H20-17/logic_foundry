# Logic Foundry

Logic Foundry is a formal proof verification system built from the ground up in Haskell. It provides a robust environment for constructing and mechanically verifying mathematical proofs from foundational axioms. The project's primary goal is to combine the rigor of classical mathematics with the expressive power and safety of a modern functional programming language.

## Core Philosophy & Design

Logic Foundry is distinguished by a unique combination of three core design principles that sets it apart from other major proof assistants.

#### 1. Foundation: ZFC Set Theory with Urelements
The system is based on classical first-order logic and **Zermelo-Fraenkel set theory with the Axiom of Choice (ZFC)**. This provides a familiar and powerful foundation suitable for formalizing the vast majority of mainstream mathematics. The logic is carefully extended to include **integer urelements** (non-set atoms), a feature handled by a core `isSet` predicate that is respected throughout the axioms.

#### 2. Architecture: LCF-style in Haskell
The implementation follows the **LCF (Logic for Computable Functions) philosophy**, where proofs are programs. By using Haskell as the meta-language, Logic Foundry empowers users to create arbitrarily complex and powerful proof automation. Proofs are constructed by composing monadic functions within a sophisticated `ProofGenTStd` environment, and the entire system is secured by a small, trusted kernel that verifies every inference step.

#### 3. Logic: The Hilbert Epsilon Operator
Foundational object constructions—those whose existence is guaranteed directly by axioms like Specification or Pairing—are all based on a single, powerful primitive: the **Hilbert epsilon operator (`εx. P(x)` or `hX`)**. This design choice results in a minimal, elegant, and consistent logical core for building sets from first principles.

## The "Theoremization" Pattern
To manage the complexity of a large mathematical library, Logic Foundry uses a formal architectural pattern for each major result. This ensures that the library is a robust, verifiable, and scalable dependency graph of proven knowledge. Each theorem is composed of three parts:

1.  **Formula Constructor:** A pure function that builds the theorem's statement as a generic sentence type `s`. It defines *what* is true.
2.  **Proof Generator:** A monadic helper that generates the formal proof of the theorem. It defines *how* the statement is proven from axioms and previously established lemmas.
3.  **Schema (`TheoremSchemaMT`):** A data structure that formally links the theorem's statement, its proof generator, and an explicit list of all required lemmas.

```haskell
-- Example of the pattern for the Binary Union Theorem
binaryUnionExistsTheorem :: s
-- ... definition of the theorem statement ...

proveBinaryUnionExistsM :: ProofGenTStd ... ()
-- ... the proof program ...

binaryUnionExistsSchema :: TheoremSchemaMT ... ()
binaryUnionExistsSchema = TheoremSchemaMT {
    lemmasM = [unionEquivTheorem, ...],
    proofM = proveBinaryUnionExistsM,
    ...
}
```

#### 4. Silent Theorems
In addition to the standard pattern, Logic Foundry supports the concept of **silent theorems**. These are complex, often computationally intensive, theorems whose full proof trace is not preserved in the final output. While the proof generator for a silent theorem still follows the 'program as proof' model and must produce a valid proof object, this object is checked for correctness at runtime and then discarded. This mechanism is crucial for managing the size of proofs, allowing for powerful automation (e.g., for arithmetic or tautology checking) without generating excessively large proof traces.

## Proof Verification and Output
The core of Logic Foundry's verification process is the generation of a formal proof object. This object is a sequence of primitive rule applications produced by the proof monad. This sequence is the **proof proper** and constitutes the formal, machine-verifiable evidence for a theorem's validity.

To aid in debugging and human understanding, the system also generates two forms of human-digestible output that render this proof trace.

#### Live Output
During proof execution, a "live" trace is printed, showing the state of the proof as it is being built. This is useful for real-time debugging of complex proof tactics.
```
┌
│0.0: FreeVar 𝑣₀    VARDEF
│┌
││0.1.0: FreeVar 𝑣₁    VARDEF
││┌
│││┌
││││0.1.1.0.0: 𝑣₁ ∉ ℤ ∧ 𝑣₀ ∉ ℤ    ASM
││││┌
│││││0.1.1.0.1.0: ∀𝑥₃(∀𝑥₂(∃𝑥₁(𝑥₁ ∉ ℤ ∧ ∀𝑥₀(𝑥₀ ∈ 𝑥₁ ↔ 𝑥₀ ∈ 𝑥₂ ∧ 𝑥₀ ∈ 𝑥₃))))    AXIOM_SPECIFICATION
...
```

#### Post-Hoc Output
After a proof is complete, a structured, indented "post-hoc" trace can be generated. This provides a clean, hierarchical view of the final proof, making it easier to analyze the logical structure of the argument.
```
0: ∀𝑥₃(∀𝑥₂(𝑥₂ ∉ ℤ ∧ 𝑥₃ ∉ ℤ → ∃𝑥₁(𝑥₁ ∉ ℤ ∧ ∀𝑥₀(𝑥₀ ∈ 𝑥₁ ↔ 𝑥₀ ∈ 𝑥₃ ∧ 𝑥₀ ∈ 𝑥₂))))    PRF_BY_UG
│0.0: FreeVar 𝑣₀    VARDEF
│0.1: ∀𝑥₂(𝑥₂ ∉ ℤ ∧ 𝑣₀ ∉ ℤ → ∃𝑥₁(𝑥₁ ∉ ℤ ∧ ∀𝑥₀(𝑥₀ ∈ 𝑥₁ ↔ 𝑥₀ ∈ 𝑣₀ ∧ 𝑥₀ ∈ 𝑥₂)))    PRF_BY_UG ◻
...
```

## Project Status
The core system is functional and has been used to prove several foundational theorems of set theory and logic. Key achievements include:

* Implementation of all ZFC axioms and a library of core logical rules.
* A robust monadic framework for proof construction with high-level tactics.
* Successful formal proofs of major theorems, including:
    * `binaryUnionExistsTheorem`
    * `crossProductExistsTheorem`
    * `specAntiRedundancyTheorem`
    * The **Principle of Strong Induction**

The successful proof of strong induction serves as a major milestone, demonstrating that the system's architecture is capable of handling complex, non-trivial mathematical reasoning.

## Getting Started
*(This section is a placeholder for future build and usage instructions.)*

To build the project, you will need the [Stack build tool](https://docs.haskellstack.org/en/stable/).

```bash
# Clone the repository
git clone <repository-url>
cd logic-foundry

# Build the project
stack build

# Run the tests
stack test
```

The primary tool for testing individual proofs is `checkTheoremM`. This function acts as a unit test for a theorem's schema; it **assumes** its lemma dependencies are already proven and runs the proof generator to verify the logic of the main theorem in isolation.

For composing proofs, the system provides `runTheoremM`. This function is intended to be used as a helper tactic within other proofs. It takes a theorem's schema and **verifies** that the required lemmas have been proven in the current context before making the theorem available.

Ultimately, the entire library can be verified from the ground up by `runProofM`. This function can verify a complete proof from the foundational axioms. The full, optimized implementation of `runProofM` (which will use `runTheoremM` internally) to intelligently avoid re-proving common theorems is a future development goal.

## Future Goals
* **Integrate LaTeX Rendering:** Enhance the human-digestible proof traces by rendering formulas using LaTeX. This will significantly improve readability for both the live and post-hoc outputs, with a particular focus on the post-hoc trace to make verified proofs resemble standard mathematical texts.
* **Expand the Mathematical Library:** Formalize the construction of fundamental mathematical objects, such as the natural numbers (ℕ), integers (ℤ), and rational numbers (ℚ).
* **Develop Advanced Automation:** Create more powerful proof tactics for simplifying complex expressions and automating common patterns of reasoning.
* **Improve User Interface:** Develop a more interactive environment for proof development, potentially with a front-end or IDE integration.

## License
This project is licensed under the MIT License. See the `LICENSE` file for details.
