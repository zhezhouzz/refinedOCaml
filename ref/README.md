# Reading notes for refinedOCaml

This directory collects papers that look relevant to the next design pass for
refinedOCaml.  The selection is intentionally biased toward:

- where to insert refinement checking after a host-language typechecker;
- modular theories, axioms, datatype encodings, and separate compilation;
- reusable refinement typing / VC-generation architecture;
- over-approximate safety vs under-approximate coverage/reachability;
- synthesis and verifier architecture ideas that may transfer to OCaml.

## Suggested reading order

### Tier 0: read first

1. [related-2025-polymorphic-coverage-types.pdf](related-2025-polymorphic-coverage-types.pdf)
   - Directly relevant to the coverage/under-approximation side.
   - Compare its type-system structure with the current whole-function
     `coverage` VC in refinedOCaml.

2. [ranjit-2025-generic-refinement-types.pdf](ranjit-2025-generic-refinement-types.pdf)
   - Most relevant for making the checker parameterized over refinement
     domains/denotations.
   - Useful for deciding what should be in stable Core vs semantic
     interpreter modules.

3. [ranjit-2024-mechanizing-refinement-types.pdf](ranjit-2024-mechanizing-refinement-types.pdf)
   - Relevant to the trusted core and proof story.
   - Good sanity check for what needs to be mechanized before the tool becomes
     more than an SMT prototype.

4. [ranjit-2023-flux-liquid-types-for-rust.pdf](ranjit-2023-flux-liquid-types-for-rust.pdf)
   - The closest analogue to grafting refinements onto a mainstream typed
     language.
   - Compare Flux's lowering/ownership-aware design with our `.cmt` Typedtree
     frontend.

5. [ranjit-2018-refinement-reflection.pdf](ranjit-2018-refinement-reflection.pdf)
   - Important for checked lemmas, reflection, and how to avoid treating all
     useful facts as trusted axioms.

6. [related-2016-program-synthesis-polymorphic-refinement-types-synquid.pdf](related-2016-program-synthesis-polymorphic-refinement-types-synquid.pdf)
   - Good background for polymorphic refinements and synthesis.
   - Also connects Ilya's synthesis line to refinement specifications.

### Tier 1: architecture and host-language integration

7. [ranjit-2017-local-refinement-typing.pdf](ranjit-2017-local-refinement-typing.pdf)
   - Relevant to local checking/inference structure and avoiding global
     inference blow-up.

8. [ranjit-2021-refinements-of-futures-past.pdf](ranjit-2021-refinements-of-futures-past.pdf)
   - Relevant to higher-order specs and implicit refinements.
   - Useful when refinedOCaml grows past first-order inlining.

9. [ranjit-2021-refinement-types-tutorial.pdf](ranjit-2021-refinement-types-tutorial.pdf)
   - Best broad refresher on LiquidHaskell-style design.
   - Useful as a reference rather than a cover-to-cover first read.

10. [ranjit-2016-refinement-types-for-typescript.pdf](ranjit-2016-refinement-types-for-typescript.pdf)
    - Useful comparison point for a refinement checker embedded into an
      existing language ecosystem.

11. [ranjit-2019-lazy-symbolic-evaluation.pdf](ranjit-2019-lazy-symbolic-evaluation.pdf)
    - Relevant to reducing VC/SMT cost through evaluation strategy.

12. [ranjit-2020-program-synthesis-type-guided-abstraction-refinement.pdf](ranjit-2020-program-synthesis-type-guided-abstraction-refinement.pdf)
    - Relevant if we want examples/witnesses or synthesis-guided coverage
      reasoning.

13. [ranjit-2025-neurosymbolic-refinement-inference.pdf](ranjit-2025-neurosymbolic-refinement-inference.pdf)
    - Relevant to future inference, but probably not the first engineering
      bottleneck.

### Tier 2: Ilya Sergey line, synthesis and verifier infrastructure

14. [ilya-2019-structuring-synthesis-heap-manipulating-programs.pdf](ilya-2019-structuring-synthesis-heap-manipulating-programs.pdf)
    - Useful for syntax-directed decomposition of heap reasoning.

15. [ilya-2020-concise-read-only-specifications.pdf](ilya-2020-concise-read-only-specifications.pdf)
    - Relevant to specification ergonomics and read-only frame-style facts.

16. [ilya-2021-certifying-synthesis-heap-manipulating-programs.pdf](ilya-2021-certifying-synthesis-heap-manipulating-programs.pdf)
    - Relevant to proof artifacts and trusting synthesized/checker-produced
      derivations.

17. [ilya-2021-deductive-synthesis-programs-with-pointers.pdf](ilya-2021-deductive-synthesis-programs-with-pointers.pdf)
    - Survey-style background for pointer/heap synthesis challenges.

18. [ilya-2023-leveraging-rust-types-for-program-synthesis.pdf](ilya-2023-leveraging-rust-types-for-program-synthesis.pdf)
    - Interesting analogue for using a host type system to guide verification
      or synthesis.

19. [ilya-2024-higher-order-specifications-deductive-synthesis-pointers.pdf](ilya-2024-higher-order-specifications-deductive-synthesis-pointers.pdf)
    - Relevant to higher-order specs and how far module/theory abstractions can
      be pushed.

20. [ilya-2025-inductive-synthesis-inductive-heap-predicates.pdf](ilya-2025-inductive-synthesis-inductive-heap-predicates.pdf)
    - Useful when thinking about inductive predicates/lemmas rather than raw
      trusted axioms.

21. [ilya-2025-inductive-first-order-formula-synthesis.pdf](ilya-2025-inductive-first-order-formula-synthesis.pdf)
    - Relevant if we later synthesize invariants or candidate refinements.

22. [ilya-2026-infinitary-relational-logic.pdf](ilya-2026-infinitary-relational-logic.pdf)
    - Potentially relevant to relational semantics for effects, exceptions,
      and under-approximation.

23. [ilya-2026-foundational-multi-modal-program-verifiers.pdf](ilya-2026-foundational-multi-modal-program-verifiers.pdf)
    - Useful for the long-term verifier architecture/proof-producing story.

24. [ilya-2026-velvet-foundational-multi-modal-verifier.pdf](ilya-2026-velvet-foundational-multi-modal-verifier.pdf)
    - Related to auto-active verifier infrastructure; lower priority for the
      current OCaml frontend.

25. [ilya-2026-lazy-proof-automation-separation-logic.pdf](ilya-2026-lazy-proof-automation-separation-logic.pdf)
    - Useful mostly for proof automation and separation-logic lemmas.

### Background outside the ten-year window

26. [ilya-2013-monadic-abstract-interpreters-background.pdf](ilya-2013-monadic-abstract-interpreters-background.pdf)
    - Outside the requested ten-year window, but directly relevant to the
      question of factoring algorithms through monadic structure.

## Mapping to refinedOCaml design questions

### A. Correct insertion point after OCaml typing

Most relevant:

- Flux: Liquid Types for Rust
- Refinement Types for TypeScript
- Local Refinement Typing
- Refinement Types: A Tutorial

Questions to extract:

- What is the stable boundary between host typed AST and refinement Core?
- How much host-language typing information should be preserved verbatim?
- What parts should be versioned per OCaml release?

### B. Modules, axioms, ADTs, and separate compilation

Most relevant:

- Generic Refinement Types
- Mechanizing Refinement Types
- Refinement Reflection
- Inductive Synthesis of Inductive Heap Predicates
- Higher-Order Specifications for Deductive Synthesis of Programs with Pointers

Questions to extract:

- Can exported `axiom`s become checked `lemma`s?
- How should `.rmi` handle abstract types, generativity, and functors?
- Should datatype axioms be sliced/configured per obligation?

### C. Parameterizing the checker by algorithm/denotation

Most relevant:

- Polymorphic Coverage Types
- Generic Refinement Types
- Monadic Abstract Interpreters
- Infinitary Relational Logic
- Foundational Multi-Modal Program Verifiers

Questions to extract:

- What is shared between safety and coverage?
- Is the shared layer an expression evaluator, a VC monad, a refinement
  denotation interface, or a bidirectional typing skeleton?
- Which pieces of coverage require a different judgment rather than merely a
  different SMT query template?

## Missing or deferred

- Ranjit Jhala's "Refinement Type Refutations" is very relevant, but the ACM
  PDF endpoint returned HTTP 403 to command-line download. Source page:
  <https://dl.acm.org/doi/10.1145/3689745>.
- Ilya Sergey's "Veil: A Framework for Automated and Interactive Verification
  of Transition Systems" was skipped because the author-site PDF repeatedly
  downloaded too slowly and produced partial files in this network session.
  Source page PDF:
  <https://ilyasergey.net/assets/pdf/papers/veil-cav25.pdf>.

## Source pages

- Ranjit Jhala publications: <https://ranjitjhala.github.io/research.html>
- Ilya Sergey publications: <https://ilyasergey.net/publications/>
- Polymorphic Coverage Types: <https://jfp.episciences.org/en/articles/17755>
- Synquid / Program Synthesis from Polymorphic Refinement Types:
  <https://arxiv.org/abs/1603.05617>
