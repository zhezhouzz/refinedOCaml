# Port scope and correspondence

Paths below refer to the pinned upstream revisions in [manifest.tsv](manifest.tsv).
Extra size, height, interval, and query arguments expose proof indices. They do
not supply an already generated target. Recursive calls construct the result;
under-summaries are usable only with decreasing measures. Contracts are checked
relative to the explicit trusted laws in each source file.

## LiquidHaskell tutorial

| Chapter | Local file / operations | Checked properties and adaptations |
| --- | --- | --- |
| 02 logic | `classics.ml`: implication, excluded middle, contradiction, De Morgan, transitivity | Boolean laws and arithmetic transitivity. |
| 03 basic | `classics.ml`: absolute, divide, truncate | Nonnegative absolute value and nonzero divisors, including the conditional division in truncate. SMT integers do not model machine overflow. |
| 04 poly | `classics.ml`: vector lookup, higher-order loop, vector sum, absolute sum | Lookup and callback index bounds, recursive loop measure, nonnegative absolute sum. Uses integer lists/accumulators as concrete instances of the tutorial's polymorphic vector/loop. |
| 05 datatypes | `classics.ml`: insert, insertion sort | Sortedness relative to a lower bound and exact length. Runtime examples also check contents. |
| 06 measure-bool | `classics.ml`: nonempty head/tail | Empty cases cannot be reached under the nonempty precondition; tail length. |
| 07 measure-int | `classics.ml`: size, sum, average, append, reverse, map, zip | Length preservation/composition, nonzero average divisor, equal zip lengths. Sum/average values are exercised at runtime, not specified by an exact sum measure. |
| 08 measure-sets | `classics.ml`: nub, append_set | Membership for an arbitrary query, union membership, nub length bound. |
| 09 lazy queues | `lazy_queue.ml`: rotate, makeq, insert, remove, replicate | Queue lengths and balance; runtime FIFO checks. Strict lists preserve values, not Haskell's lazy cost bound. |
| 10 associative maps | `associative_map.ml`: set, get, mem | Ordered search-tree insertion/update; arbitrary-key membership and value preservation, overwrite value, size bound, safe lookup. Keys/entries are integers. |
| 11 pointers | `classics.ml`: set_at, peek_at, poke, peek, zero_fill | Offset bounds and buffer length through recursive writes. A reference to a list models the buffer; runtime checks partial zero-fill and preserves the prefix. Does not model foreign pointers, byte layout, or memory allocation. |
| 12 AVL | `avl.ml`: node, balance, insert | Ordering, cached heights, AVL balance, insertion height bound. Runtime checks all four rotation cases and contents. Deletion is outside this port; insertion set preservation is runtime-checked. |

## CoverageType generators

All local names in this table are in `coveragetype/`. Rows grouped together
still have individual source mappings in the manifest.

| Upstream source | Local file / algorithm | Target and adaptation |
| --- | --- | --- |
| basic/boundlist | `boundlist.ml`: bound_list_gen | Recursive exact length with every element above the universal floor. |
| basic/duplicate_list | `duplicate_list.ml`: duplicate_list_gen | Recursive repetitions of the universal item. |
| basic/sortedlist_simpl | `semantic_lists.ml`: list_exact, sortedlist_simpl | Builds arbitrary tails recursively and adds an arbitrary head, as the source does. Its image includes sorted lists of the specified length; not all outputs are sorted. |
| elrond/UniqueList | `semantic_lists.ml`: unique_list_port | Recursive tail, arbitrary head, absence filter, rejection; covers all unique lists of the given length. |
| quickchick/SizedList, SortedList | `semantic_lists.ml`: sized_list_port, sorted_list_port | Early-empty size bound; recursive lower-bound filter for exact sorted length. |
| elrond/stream | `semantic_stream.ml`: stream_port | Recursive finite streams with a length bound. Strict constructor spine replaces stream suspensions. |
| elrond/BankersQueue, BatchedQueue | `semantic_bankers_queue.ml`, `semantic_batched_queue.ml` | Choose rear size and recursively generate both sequences. Front size is fixed and rear is shorter in the target. At size zero the target is empty; the executable empty queue is still retained. Cached sizes remain in BankersQueue. |
| elrond/LeftistHeap | `leftist_heap.ml`: generate | Recursive left/right generation, rank and leftist invariant, universal depth. Range selection has a separately checked summary. |
| elrond/UnbalanceSet | `semantic_bst.ml`: unbalanced_set_port | Recursive search-tree generator with depth and strict key intervals. |
| leonidas/SizedBST | `semantic_bst.ml`: sized_bst_port | Depth-bound generator, root range choice, recursive narrowed intervals. |
| quickcheck/SizedSet | `semantic_bst.ml`: sized_set_port | Recursive ordered set, interval width decreases. |
| leonidas/CompleteTree | `semantic_complete_tree.ml`: complete_tree_port | Both subtrees recursively have the required exact height. |
| quickcheck/SizedHeap | `semantic_sized_heap.ml`: sized_heap_port | Recursive heap with a strict maximum and depth bound; impossible sampled keys reject. |
| quickchick/RedBlackTree | `semantic_red_black_tree.ml`: red_black_tree_port | Black height, no red/red edges, allowed root color, all recursive color cases. Measure encodes height and color. |
| quickchick/SizedTree | `semantic_sized_tree.ml`: sized_tree_port | Recursive arbitrary labels and both children with early-empty branches. |
| stlc/gen_term_size, stlc/stlc | `semantic_stlc.ml`: vars_with_type, gen_term_no_app, gen_term_size_port, stlc_port | Context, target type and application count are universal. Recursive applications/abstractions use a lexicographic measure and preserve rejection. Arbitrary type generation is an upstream library primitive. |
| monad/case1 | `semantic_monad_case1.ml`: bind/return/fmap/union and monad_case1 | Executes thunk/callback composition; covers the source's asserted result 2. |
| monad/test | `semantic_monad_return.ml`: monad_test | Polymorphic executable return; exact returned value. Runtime instances include integer and Boolean values. |
| monad/coverage_monad_library | `semantic_monad_library.ml` | Executable return, bind, fmap/fmap2, union, fix, ranges, nat, pair, option, oneof, nil/cons generators, list selection, frequency, numeral, repetition, positive split. SMT checks concrete indexed instances of 17 coverage contracts and a recursive higher-order fix instance. Runtime checks also exercise selection, repetition, failure, and both union/option branches. This does not establish the source's universally quantified arbitrary-predicate schemas. Digits use character codes; `choose_by_fq` is modeled by its supported indices. The source itself uses Boolean selection in frequencyl_aux. |
| monad/herdtools7 | `semantic_herdtools.ml`: bits_gen, herdtools7 | All five literal variants and recursive bitvectors. String and real library payloads use opaque integer identities, not byte-level string or IEEE arithmetic semantics. |
| monad/tezos_test | `semantic_tezos_test.ml` | Recursive byte strings, operation payload sizes, bounded rational pairs, recursive rational lists, and all priority variants. operation_gen also runs the supplied block-hash callback. |
| monad/tezos | `semantic_tezos.ml`: common generators plus tezos_tree_gen | Generates trees by recursive sequence splitting, preserving preorder. Concrete prefix/suffix functions model upstream list_split_n; empty/singleton/unary/binary cases remain. |
| monad/tree2list | `semantic_tree2list.ml`: append, flatten, list_gen | Corrected preorder flatten recursively visits both children. Safety checks contents and length; coverage constructs a right-spine witness for any list. Upstream arbitrary tree generation remains a library primitive. See correction below. |
| monad/vellvm | `semantic_vellvm.ml`: gen_uvalue/gen_values | Mutually recursive scalar/array/vector generation; exact element counts and recursive typing. Retains source rejection for unsupported types and source bounds of 10000 for i32/i64. Does not claim coverage of all LLVM values. |
| monad/xen_api | `semantic_xen_api.ml` | Finite sizes/kinds/timeouts, recursively repeated fd specs, and fd construction. Time values use integer milliseconds. Abstract library kinds use indices 0–5; delay generation is concretized as None at zero size or a delay in the chosen total bound. Properties refer to this explicit library model, not the external Xen runtime. |
| monad/zipperposition | `semantic_zipperposition.ml`: default_fuel, zipperposition | Corrected bounded recursive terms with variables, two binary symbols, two unary symbols, and conditionals. Symbol/name strings use finite indices. Fuel coverage implies the exact-size lower bound in this model, whose size counts one node per constructor and excludes function-symbol payloads (the upstream size predicate is abstract). Supported alternatives, not frequency weights, are modeled. See correction below. |

## Upstream body corrections

`tree2list.ml`'s active flatten ignores the left child. The port retains this
behavior as `upstream_flatten`: a three-node tree yields only two list elements.
The corrected flatten yields all three in preorder. This demonstrates a
traversal defect; it does not imply the original unindexed lower bound “all
lists are reachable” is false, because right spines can still produce any list.

`zipperposition.ml` binds `self = default_fuel (n - 1)` before testing `n <= 0`.
In strict OCaml even `default_fuel 0` never reaches the base test. The standalone
`upstream_zipperposition_failure.ml` preserves that construction-time recursion
and requires a stack-overflow reproduction. The verified port tests the base
case first and recurses only when generating the selected constructor's
children. Runtime examples cover every symbol alternative. These two rows are
`corrected-verified`, not claims that the untouched source bodies passed.
