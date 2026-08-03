# Prompt

<!-- codex-project-policy:compression-v1 -->
## Compression, randomized breadth, and memory

- Give reuse, simplification, and deletion equal consideration to addition. Finish each task with an obsolescence audit covering code, tests, comments, docs, configuration, and tracked work.
- Remove replaced behavior throughout the owned scope unless a verified compatibility, migration, rollback, history, or provenance obligation requires both; name that obligation and removal gate.
- Avoid comments that narrate obvious function-body behavior. Remove stale comments and completed TODOs while preserving non-obvious intent, safety, interoperability, and provenance.
- Use seeded recursive partition search or Verbalized Sampling only for bounded open-ended diversity work. Record universe, coverage, candidate set/path, and draws; never claim uniformity without proof or use it for deterministic gates.
- Keep memory content separate from reference-recency metadata. Recency may delay compression but never outranks authority, corrections, or explicit retention; GC proposals remain advisory and non-destructive.

Solve the HVM4 MOV vs DUP bounty (end-to-end)

Operate as a specialist in **HVM4 / Interaction Calculus / interaction nets** and low-level evaluator debugging (C). You are given a short interaction-nets context dump and a summary/outline of prior engineering progress. The context dump is part of this guide and also exists in `InteractionNets_Long.md`; a shorter version is available in `InteractionNets_Short.md`.

Your mission is to **fully solve** the bounty, in the **strict** interpretation: identify the root cause of the MOV-vs-DUP divergence, implement a correct fix/version, and PROVE it by running the code/tests in the local workspace. You are *not* preparing the PR yet, but you must work as if a PR is the next step.

Proving success is non-negotiable, you must continue working until success is proven. Proving requires the DUP and MOV versions of all test scripts have their output match EXACTLY. A matching structure or matching data does NOT qualify, they must be PROVEN identical by visual EXACT match or code.

A summary of how MOV works(/ed) and previous failed attempts and current "working" solution (that doesn't match the strict bounty interpretation) is below.

This is an incredibly hard problem. You must persist until all of the above succeed EXACTLY. It will likely take hours of work at minimum to achieve this.

---

# Workspace layout (critical)

You have these folders in your working repository:

* `hvm4_static/` — **your working copy** of HVM4.
  ✅ You **must** build, run, instrument, and edit **only this** to implement and validate the fix.

* `HVM_static/` — working copy of HVM2 repo (may be useful for conceptual reference).

* `Bend_static/` — working copy of Bend repo (may be useful for conceptual reference).

You also have **clean reference submodules**:

* `hvm4/` — reference only (do **not** modify)
* `HVM/` — reference only (do **not** modify)
* `Bend/` — reference only (do **not** modify)

**Hard rule:** Do **not** edit any file inside the submodules (`hvm4/`, `HVM/`, `Bend/`).
You may diff against them, read them, and use them as a “known-good” baseline.
If you solve the bounty, I will make a separate request to prepare a PR for the upstream hvm4 repo (you'll be allowed to edit the submodule then, of course).

---

## The bounty statement

> HVM4 recently introduced **MOV nodes**, meant to allow using a variable more than once in **different branches** without an extra lam/dup node, reducing interactions.
> Sadly, on the counterexample below, using DUP nodes and using MOV nodes gives **different answers**.
> There are two possibilities:
>
> * the implementation is wrong (most likely), or
> * the concept is wrong (if so, explain why).
>
> Goal: implement a solution in HVM4 such that:
>
> 1. both encodings produce the **same output** on the test program when run with `-C1`, and
> 2. the MOV-optimized version halts in **< 50k interactions**.
>
> The solution must be correct: using MOV nodes and DUP nodes to pass a value to different branches must produce the exact same output.
> The final result should be submitted as a PR (later). For now, you must fully solve and demonstrate locally.

---

## The failing test program. Also included in hvm4_static/test/bounty_failure.hvm4 and bounty_failure_dup.hvm4

```hvm
// PROBLEM: in the code below:
// 1. both versions of @insert should output the same result with -C1
// 2. the second version should take <50k interactions to halt
// yet, on HVM4's current MOV node implementation, the outputs mismatch. why?
// your goal is to find out, and fix HVM4 so that both points above hold.
// $10k bounty: https://x.com/VictorTaelin/status/2006818916211834900

@tail = λ{[]:[];<>:λa.λb.b}

// List ::= Cons List | Succ List | Nil
@C = λt. λc. λs. λn. c(t)
@S = λp. λc. λs. λn. s(p)
@N =     λc. λs. λn. n

// Bits ::= O Bits | I Bits | E
@O = λp. λo. λi. λe. o(p)
@I = λp. λo. λi. λe. i(p)
@E =     λo. λi. λe. e

// ℕ → U32 → Bin -- converts a U32 to a Bin with a given size
@bin = λ{
  0n: λn. λo.λi.λe.e;
  1n+: λ&l. λ&n. (λ{
    0: λo.λi.λe.o(@bin(l, n/2))
    1: λo.λi.λe.i(@bin(l, n/2))
  })(n % 2)
}

// Bin → (P → P) → P → P -- applies a function N times to an argument
@rep = λxs.
  ! O = λp.λ&f.λx.@rep(p,λk.f(f(k)),x)
  ! I = λp.λ&f.λx.@rep(p,λk.f(f(k)),f(x))
  ! E = λf.λx.x
  xs(O, I, E)

// [1,2,3] ::= Cons (Succ (Cons (Succ (Succ (Cons (Succ (Succ (Succ Nil))))))))
@to_nats_go = λxs. λn.
  ! C = λt. λn. n <> @to_nats_go(t, 0n)
  ! S = λp. λn. @to_nats_go(p, 1n+n)
  ! N = λn. [n]
  xs(C, S, N, n)

@to_nats = λxs.
  @tail(@to_nats_go(xs,0n))

@view = λxs.
  ! O = λp. #O{@view(p)}
  ! I = λp. #I{@view(p)}
  ! E = #E
  xs(O, I, E)

// control: using DUP nodes (this works)
@insert_A = λn.
  ! O = &{}
  ! I = (λ&p. λxs. λ&o. λi. λe.
    ! O = λxs. o(@insert_A(p, xs))
    ! I = λxs. i(@insert_A(p, xs))
    ! E = o(@insert(p, @N))
    xs(O, I, E))
  ! E = λxs. λo. λ&i. λe.
    ! O = λxs. i(xs)
    ! I = λxs. i(xs)
    ! E = i(@N)
    xs(O, I, E)
  n(O, I, E)

// problem: using MOV nodes (this fails)
@insert_B = λn.
  ! O = &{}
  ! I = (λ&p. λxs. λ&o. λi. λe.
    % f = o
    ! O = λxs. f(@insert_B(p, xs))
    ! I = λxs. i(@insert_B(p, xs))
    ! E = f(@insert_B(p, @N))
    xs(O, I, E))
  ! E = λxs. λo. λ&i. λe.
    % k = i
    ! O = λxs. k(xs)
    ! I = λxs. k(xs)
    ! E = k(@N)
    xs(O, I, E)
  n(O, I, E)

// this should produce the same output with either @insert fns above when
// running it with `HVM4 -C1`, but, currently, the outputs mismatch...
@main =
  ! ins = @insert_B(@I(@I(@I(@I(@E)))))
  @view(@rep(@bin(16n,512), ins, @O(@O(@O(@O(@O(@O(@E))))))))


---

## External Repos Guidance

Static copies live in `Bend_static/`, `HVM_static/`, and `hvm4_static/` and are used for local testing; edits are allowed there.
Submodules live in `Bend/`, `HVM/`, and `hvm4/` and should not be modified unless you are explicitly preparing a PR to those upstream repos.

---

# DETAILED MOV EXPLANATION, PREVIOUS ATTEMPTS, ETC.:

# MOV Detailed Handoff (2026-01-13)

This is a detailed handoff for MOV work in this repo copy. It focuses on the
HVM4 runtime implementation and test behavior, not on explaining HVM or IC.

Dialect lock-in: this document is about **HVM4 Interaction Calculus** and the
`hvm4_static/clang` runtime. When describing concrete rules or node taxonomy,
this doc tags provenance inline as (HVM4 docs) or (source code).

---

## 1) Intent of MOV (HVM4, high level)
- MOV is intended as a **sharing operator** that lets a value be reused across
  branches without explicit DUP nodes, reducing interactions in the happy path.
  (HVM4 docs)
- MOV-bound variables are **affine by default**, but the docs note they may
  appear multiple times and the parser does **not** enforce branch separation.
  (HVM4 docs)
- That means MOV is *not* automatically safe: if a MOV-bound value ends up
  sharing a **mutable binder slot** across multiple uses, semantics can change.

---

## 2) How MOV is implemented (runtime structure)

### 2.1 Core runtime shapes (HVM4 runtime)
- MOV term: `MOV(val, body)` stored in heap with ext used as label base.
- GOT term: a linked MOV variable that points to the MOV value slot.
- DUP/DP0/DP1 are explicit duplication terms; MOV has no label itself.
(source code)

### 2.2 Parser lowering for MOV
- `% x = v; body` parses into a MOV term with `val = v` and `body = body`.
- MOV-bound variable occurrences become BJM in quoted/static contexts; they are
  mapped to GOT during ALO instantiation. (source code)
- The parser now **reserves a label range** in MOV ext when uses > 1, but does
  **not** rewrite the term into DUP/let. (source code)

### 2.3 WNF evaluation flow for MOV
- WNF entry on MOV evaluates the **body** (not the value) and then lets GOT
  interact with the WHNF of the bound value. (source code)
- GOT dispatch uses MOV rules based on the WHNF tag. The core interactions:
  - MOV-LAM: build a lambda that points to a fresh GOT and bind its body to a
    new slot, then (optionally) memoize. (source code)
  - MOV-SUP: build a SUP where each branch is a GOT of the corresponding child.
    (source code)
  - MOV-NOD: rebuild a node with GOTs for each field. (source code)
  - MOV-RED/MOV-DRY/MOV-NAM: rebuild wrapper terms with GOTs. (source code)
  - MOV-MOV: collapse two MOV binders into one by moving the value. (source code)
- ALO-MOV instantiates a dynamic MOV from a book term; now preserves MOV ext
  labels so runtime rewrites can reuse parser-reserved labels. (source code)

### 2.4 SAFE_MOV policy
- SAFE_MOV is a runtime flag (default on via `HVM4_SAFE_MOV`).
- When SAFE_MOV is on, MOV results are **not memoized** for LAM/NOD/SUP/RED/
  DRY/NAM. This avoids sharing a mutable binder slot across uses. (source code)

### 2.5 MOV guard (runtime rewrite to DUP)
- A runtime guard scans the MOV body to count usage of the MOV variable.
- If usage is unsafe, it **rewrites the MOV body into an explicit DUP chain**:
  each MOV use becomes DP0/DP1, and a DUP chain provides the split. (source code)
- It uses parser-reserved labels (MOV ext) when present, else allocates fresh
  labels at runtime. (source code)

---

## 3) Current code state in this workspace
These are the changes that are *currently active*:

### 3.1 MOV guard integrated (runtime)
- `hvm4_static/clang/wnf/mov_guard.c`
- `hvm4_static/clang/wnf/_.c`
- Guard invoked when entering MOV body in WNF (SAFE_MOV only).

### 3.2 Parser label reservation (no rewrite)
- `hvm4_static/clang/parse/term/mov.c`
- MOV ext stores a base label if uses > 1.

### 3.3 ALO-MOV label propagation
- `hvm4_static/clang/wnf/alo_mov.c`

### 3.4 SAFE_MOV memoization policy
- `hvm4_static/clang/wnf/mov_lam.c`
- `hvm4_static/clang/wnf/mov_nod.c`
- `hvm4_static/clang/wnf/mov_sup.c`
- `hvm4_static/clang/wnf/mov_red.c`
- `hvm4_static/clang/wnf/mov_dry.c`
- `hvm4_static/clang/wnf/mov_nam.c`

### 3.5 Printer SUB masking (mitigation)
- `hvm4_static/clang/print/term.c`
- `print_term_at` now clears SUB before printing instead of asserting.

---

## 4) Test inventory (what exists now)

### 4.1 All `hvm4_static/test/mov_bounty*.hvm4` files
- `hvm4_static/test/mov_bounty.hvm4`
- `hvm4_static/test/mov_bounty_dup.hvm4`
- `hvm4_static/test/mov_bounty_f3.hvm4`
- `hvm4_static/test/mov_bounty_f3_dup.hvm4`
- `hvm4_static/test/mov_bounty_min.hvm4`
- `hvm4_static/test/mov_bounty_min_dup.hvm4`
- `hvm4_static/test/mov_bounty_small.hvm4`
- `hvm4_static/test/mov_bounty_small_dup.hvm4`
- `hvm4_static/test/mov_bounty_tiny.hvm4`
- `hvm4_static/test/mov_bounty_tiny_dup.hvm4`

Root-level copies for reference:
- `mov_bounty_f3.hvm4`
- `mov_bounty_f3_dup.hvm4`

### 4.2 Other MOV-related tests in `hvm4_static/test`
- `mov_dup_func.hvm4`
- `mov_dup_nested.hvm4`
- `mov_dup_test.hvm4`
- `mov_erase_test.hvm4`
- `mov_erase_test_dup.hvm4`
- `mov_lam_bench.hvm4`
- `mov_lam_bench_dup.hvm4`
- `mov_lam_dupvar.hvm4`
- `mov_lam_erase_bench.hvm4`
- `mov_lam_erase_bench_dup.hvm4`
- `mov_lam_test.hvm4`
- `payor_new.hvm4`
- `payor_new_dup.hvm4`
- `payor_repro.hvm4`
- `payor_repro_dup.hvm4`
- `new_issue.hvm4`

### 4.3 WIP programs (MOV vs DUP) - also must pass (match output and preferably be faster than DUP versions)
- `hvm4_static/wip/mov_0.hvm4`
- `hvm4_static/wip/mov_1.hvm4`
- `hvm4_static/wip/mov_2.hvm4`
- `hvm4_static/wip/mov_3.hvm4`
- `hvm4_static/wip/mov_4.hvm4`
- `hvm4_static/wip/mov_0_dup.hvm4` ... `mov_4_dup.hvm4`

### 4.4 Scripts
- `mov_lam_bench.sh`
- `mov_vs_dup_slow.sh`
- `payor_new.sh`

### 4.5 Root-level repros and notes
- `payor_new.hvm4` (root) and `new_issue.hvm4` (root) are mirrors used
  during debugging.
- `payor.hvm4` is a conceptual derivation and is **not** runnable
  (parse error by design).

### 4.6 Tests not yet present but worth adding
- A runnable version of the `payor.hvm4` conceptual example.
- A test that isolates MOV with ALO / book instantiation (ALO-MOV path).
- A collapse-order test that checks -C1 vs -C2 output ordering for MOV.

---

## 5) Verified outcomes in this workspace (current)
Built with `gcc -O2` in `hvm4_static/clang`.

### payor_new
```
main.exe ..\..\payor_new.hvm4 -C -s
```
Output: `lambda a.a`
Itrs: 77

### new_issue
```
main.exe ..\..\new_issue.hvm4 -C -s
```
Output:
`#T{#O{#O{#I{#E{}}}},#O{#O{#I{#E{}}}},#O{#O{#I{#E{}}}},#O{#O{#I{#E{}}}}}`
Itrs: 1155

### wip MOV vs DUP
Outputs match under `-C`, interaction counts:
- mov_0: MOV 1279, DUP 1197
- mov_1: MOV 11364, DUP 11102
- mov_2: MOV 13668259, DUP 10227073
- mov_3: MOV 19, DUP 17
- mov_4: MOV 3, DUP 3

### bounty
```
main.exe ..\test\mov_bounty.hvm4 -C1 -s
main.exe ..\test\mov_bounty_dup.hvm4 -C1 -s
```
- MOV: 20701 interactions
- DUP: 97885 interactions
- Outputs match.

---

## 6) Older MOV fix attempts and what they imply (from various tracking documents i the root of hte repo)

### 6.1 `bounty_investigation_summary.md`
Highlights:
- The earliest failure was tied to **3+ uses** (nested DUP chain).
- Experiments added DUP-MOV/GOT interactions and MOV gating under DUP.
- Gating MOV under DUP caused crashes; pre-emptive DUP-MOV was stable but
  still incorrect for `mov_bounty_f3`. (doc)

### 6.2 `investigation_summary_latest.txt`
Highlights:
- Pre-emptive DUP-MOV in WNF was tried; label-capture issues suspected.
- Fresh-label experiments in DUP-MOV fixed `mov_bounty_f3` but broke bounty.
- Suggestion: label-renaming strategy in DUP-MOV to avoid capture. (doc)

### 6.3 `bounty_proof_report.md`
Highlights:
- Earlier “solution” combined SAFE_MOV with a **parser rewrite** for payor_new
  (cloned-let fallback) and auto-dup for uses>2.
- This is now considered a **workaround** because it shifts correctness to the
  parser. The current state removes that parser rewrite. (doc)

### 6.4 `pr_diff_summary.md`
Highlights:
- Summarizes a prior patchset: SAFE_MOV + auto-dup uses>2, cleanup traces.
- Reported passing `_all_.sh` in that environment. (doc)

### 6.5 `progress_notes.txt`
Highlights (timeline):
- Experiments with MOV-LAM body cloning (caused OOM on new_issue).
- GOT split-on-use attempts (reverted).
- Multiple cycles of parser fallback vs runtime-only fixes.
- Added wip DUP variants and verified MOV vs DUP outputs match. (doc)

### 6.6 `bounty_guidance.txt`
Highlights:
- Clarifies the success criteria: -C1 output equality and <50k MOV itrs.
- Emphasizes collapse-order sensitivity: -C1 means the **first** CNF line.
- Notes label semantics and SUP lifting behavior. (doc)

### 6.7 `code_changes_bundle.txt`
Highlights:
- Captures an older snapshot of key code sections (SAFE_MOV + DUP-MOV, etc.).
- Useful for diffing historical states. (doc)

Important note:
These docs describe **older states**. Several of those changes were reverted.
Always verify against current code under `hvm4_static/clang`.

---

## 7) What worked vs what didn’t (current view)

### 7.1 Worked (current state)
- Runtime MOV guard rewrite to explicit DUP when unsafe -- this probably qualifies as a "work-around"
- SAFE_MOV memoization avoidance for MOV-LAM/NOD/SUP/RED/DRY/NAM.
- ALO-MOV label propagation.
- MOV vs DUP outputs match on:
  - payor_new
  - new_issue
  - wip mov_0..mov_4
  - bounty program (and MOV stays < 50k itrs)

### 7.2 Did not work or was reverted
- Parser rewrite fallback (cloned-let) for MOV violations: deemed workaround.
- MOV-LAM body cloning via deep rebind: caused OOM on new_issue.
- GOT split-on-use inside WNF: unstable and not necessary with guard.
- Gating MOV under DUP frames: led to crashes/stack corruption.
- DUP-MOV label experiments: fixed f3 but broke bounty (label capture).

---

## 8) Remaining issues and TODOs
1) Windows test runner: `hvm4_static/test/_all_.ps1`
   - Run from repo root: `powershell -ExecutionPolicy Bypass -File hvm4_static\test\_all_.ps1`
   - Requires a toolchain with pthreads (MinGW-w64 or LLVM MinGW in PATH).
2) Expand the MOV guard analysis to preserve more MOV wins while safe.
3) Revisit printer SUB masking; it hides invariant violations.
4) Add missing test(s): runnable payor example, ALO-MOV specific tests.

---

## 8a) Bounty interpretation: no MOV->DUP fallback allowed
If we assume the stricter interpretation that **MOV must remain native** and
must **never** be replaced with DUP (runtime or parser), then:

- The current runtime guard **does not qualify** as a final solution because
  it explicitly rewrites unsafe MOV bodies into a DUP chain.
- Any parser fallback that rewrites MOV to cloned-let + auto-dup is also
  disallowed for the same reason.

Under this interpretation, the required direction is:
1) Keep MOV native in all cases (no fallback to DUP chains).
2) Prove or enforce correctness by **native MOV interactions** only, i.e.,
   by fixing MOV’s own rewrite rules, substitution handling, or label
   discipline so that MOV and DUP are observationally equivalent for all
   programs without turning MOV into DUP.

Implication: the current state is a correctness safety net, but it is not a
“native MOV” solution. It is a practical fix for output equivalence, not the
final form demanded by the strict bounty reading.

---

## 9) Quick commands (current)
Build:
```
cd hvm4_static/clang
gcc -O2 -std=c11 -o main.exe main.c
```

payor_new:
```
main.exe ..\..\payor_new.hvm4 -C -s
```

new_issue:
```
main.exe ..\..\new_issue.hvm4 -C -s
```

bounty:
```
main.exe ..\test\mov_bounty.hvm4 -C1 -s
main.exe ..\test\mov_bounty_dup.hvm4 -C1 -s
```

wip comparison:
```
main.exe ..\wip\mov_2.hvm4 -C -s
main.exe ..\wip\mov_2_dup.hvm4 -C -s
```

all tests (Windows):
```
powershell -ExecutionPolicy Bypass -File hvm4_static\test\_all_.ps1
```

---

# CONTEXT DUMP

---

﻿0) Scope, notation, and guardrails
Context-dump playbook for:
    • Interaction nets (Lafont), interaction systems, interaction combinators.
    • Textual calculi for nets (Fernández–Mackie, lightweight).
    • λ-calculus sharing + dup/erase + (near-)optimal reduction.
    • Implementing/debugging net/IC evaluators & compilers (C/Rust): rule compilation, memory layout, scheduler correctness, perf instrumentation.
    • HigherOrderCO ecosystem, esp. HVM4 / Interaction Calculus.
Scope clarifiers
    • Not a tutorial; dense reminder system for future work.
    • Prefer primary sources; this file is memory aid, not authority.
    • Keep HVM2 (interaction combinators) vs HVM4 (Interaction Calculus) distinct: different syntax/runtime invariants.
Role identity
    • You are GPT-5.2-Codex. Operate as a specialist assistant for interaction nets/combinators, textual interaction calculi (Fernández–Mackie tradition and modern variants), λ-calculus sharing/duplication/erasure/(near-)optimal reduction, and low-level runtimes/compilers (C/Rust), including the HigherOrderCO ecosystem (HVM2/HVM4/Bend).
Notational conventions
Interaction nets (graph)
    • Agent symbols α,β,γ; arity ar(α)=n ⇒ n aux + 1 principal port.
    • Ports: principal 0; auxiliary 1..n.
    • Wire: undirected; each port degree=1.
    • Active pair: α0—β0 (principal–principal).
Textual net calculi (FM/lightweight)
    • Names x,y,z are wires; multiplicity restricted.
    • Terms α(t1..tn): tree rooted at α principal; subterms to aux ports.
    • Equations t = u: wire connecting roots’ principals.
    • Configurations ⟨interface | Δ⟩ with Δ multiset of equations.
HOC Interaction Calculus (HVM4 surface)
    • Vars affine by default.
    • Multi-use via explicit dup/sup or parser auto-dups.
    • Labels L,R,... govern dup/sup (equal vs unequal).
HVM2 Interaction Combinators (textual IR)
    • Core nodes CON/DUP/ERA; extensions REF/NUM/OPR/MAT.
      (Bend→HVM2 lowering describes 7 node kinds total: Eraser, Constructor, Duplicator, Reference, Number, Operation, Match; numeric “switch” is expressed via MAT wiring rather than a distinct SWI node kind in that presentation.)
    • Principal port implicit; active pairs written as root ~ root.
    1. Graph vs syntax identity: two x can mean same node or two copies (formalism-dependent).
    2. Locality ≠ strategy-free: strong confluence ⇒ permutation equivalence, not termination/cost/readback order.
    3. Readback is part of observed semantics (collapse/quote matters).
    4. Optimization ≠ semantics unless proven; MOV-like nodes are conditional.
    5. Parser desugarings matter (auto-dup/fork labels); don’t reason from surface only.
    6. Scopeless vars are real wires; unused binder ⇒ erasure, not regular var.
    7. HVM2 vs HVM4 is a hard boundary; don’t transpose rules.

Notation contract (avoid syntax/precedence mistakes)
This document uses three distinct notations; never mix them inside a single example without declaring it:

A) “Theory/core application notation”:
   - Application is written explicitly as (f x) or (f)(x).
   - β-like patterns must be parenthesized: (λx.body)(arg).

B) “HVM4 parser notation”:
   - No whitespace application. Use f(a) (and f(a,b) as nesting sugar).
   - Lambdas are written λx. body (or λx,y. body).
   - Always parenthesize when showing rewrite LHS/RHS if ambiguity is possible.

C) “Implementation pseudocode”:
   - C/Rust-like; explicit pointers/ports/heap slots.

Rules:
- When showing a rewrite rule, always use fully parenthesized LHS patterns.
- When showing HVM4 surface code, always use f(a) style (never f a).
- If you’re showing “theoretical IC” rules, label the block as THEORY NOTATION, and don’t rely on HVM4 parsing precedence.

Dialect lock-in + provenance discipline (required)
Before asserting *any* of the following: node kinds, rewrite rules, syntactic sugar/desugaring, or “stuck vs error” behavior, first lock the dialect:

1) Interaction Nets (Lafont-style): agents with explicit principal/aux ports; active pair = principal–principal.
2) Textual net calculi (Fernández–Mackie / lightweight): names-as-wires with multiplicity constraints; equations represent principal wiring; “communication/substitution/interaction” step taxonomy.
3) HVM2 / Interaction Combinators runtime: ERA/CON/DUP core with REF/NUM/OPR/MAT extensions as described by HVM2/Bend docs; principal port is implicit; reduction uses LINK/CALL/COMMUTE/ANNIHILATE/etc.
4) HVM4 / HigherOrderCO Interaction Calculus: affine vars + explicit DUP/SUP labels + MOV; evaluation produces IC structures; collapse/CNF readback quotes vars and lifts SUPs.

Provenance rule:
- If you state a concrete rewrite rule or node taxonomy, attach a provenance marker in-line:
  (a) “theory” (paper/presentation), (b) “HVM2 paper”, (c) “Bend docs”, (d) “HVM4 docs/rule file”, or (e) “source code”.
- If you can’t attach provenance immediately, mark the claim as: VERIFY (do not present it as fact).

Hard boundary rule:
- Never transplant node names or rewrite rules across HVM2↔HVM4 without an explicit mapping argument. If a concept exists in both systems (e.g., “duplication”), treat it as an analogy until you’ve checked the exact node/tag/rule set.

Always-on mental model & invariants
    • Graph, not tree: reason in ports/wires; sharing is graph identity + explicit dup/erase/move machinery.
    • Locality + interface preservation: rewrite only active pair; RHS reconnects each free port exactly once; no multi-connect/dangling.
    • Strong confluence caveat: one rule per unordered pair ⇒ unique normal forms (if any), not termination/cost/readback order.
    • Linearity / name discipline (formalism-specific):
        ◦ FM-style textual calculi: names model wires; internal names occur exactly twice; interface/free names occur once.
        ◦ HVM4 IC: regular variables (VAR) are affine (0 or 1 occurrence). Multi-use must be made explicit via DUP/SUP (including parser auto-dups) or via MOV-bound variables under their side-conditions (branch separation is not enforced by the parser).
        ◦ “Missing ERA” corresponds to *discarded* resources/arguments (0-use) in a setting that otherwise requires explicit consumption.
    • Bend/HVM2 gotcha: duplicating a duplicating var can misbehave; keep single dup source or linearize.
    • Labels matter: equal labels annihilate pairwise; different labels commute (cross product).
    • Linked vs quoted: linked vars/binders use SUB cells; quoted vars/binders (de Bruijn) used for readback; collapse order matters.
    1. Identify formalism: IN/IC/ICalculus/HVM4? Normalize notation (ports, arities, labels).
    2. State the rule set explicitly; never guess. If ambiguous, list candidates + consequences.
    3. Check invariants: port degree/interface, name multiplicity, label discipline, runtime invariants (SUB/atomic link/heap ownership).
    4. Reduce only active pairs; track wiring; re-check interface + multiplicity after each rewrite.
    5. Try to break it: smallest counterexample (label mismatch, nested dup, mov-in-branch, readback diff).
    6. Then discuss implementation: data structures, instrumentation, diff-debugging.
When in doubt
    • Never invent a rewrite rule or port ordering; locate spec/diagram.
    • Don’t conflate evaluation with readback; outputs can differ by collapse order.
    • Treat MOV ≡ DUP as a hypothesis requiring proof or differential testing.
    • Define performance metrics (interactions vs admin); align instrumentation.
    • Assume concurrency races until proven; require atomicity/ownership arguments.

1) Concept map / knowledge graph
Node glossary
    • λ-calculus (β-reduction)
    • Sharing graphs / graph reduction
    • Lévy optimal reduction
    • Lamping-style algorithms
    • Linear logic / proof nets
    • Geometry of Interaction (GoI)
    • Interaction nets (Lafont)
    • Interaction systems (Σ, rules)
    • Interaction combinators (ε/δ/γ)
    • Textual interaction calculi for nets (Fernández–Mackie, lightweight)
    • Explicit substitutions / indirections
    • Scheduler (active pair selection)
    • Rule compilation (pattern → RHS construction)
    • Memory model (ports, wires, substitution cells, heap)
    • Readback (quoting, collapse/CNF)
    • HigherOrderCO Interaction Calculus (IC)
    • HVM2/HVM4 runtime architecture (parallelism, atomic interactions)
    • MOV vs DUP optimization/equivalence
    • HVM2 interaction table (link/call/erase/commute/annihilate)
    • HVM4 core syntax + parser desugaring (auto-dup, fork sugar)
    • Dynamic labels (DSU/DDU) and label evaluation
    • Static vs dynamic terms (book/heap, ALO instantiation)
    • Bend (high-level language → HVM2 nets)
    • Collapser / CNF queue discipline (ordering artifacts)
Edges (constraints)
    • λ-calculus → sharing graphs: avoid duplicating work via graphs.
    • Sharing graphs → dup/erase machinery: multi-use & unused vars need explicit nodes.
    • Linear logic/proof nets ↔ interaction nets: local rewrites correspond to proof-net moves.
    • Interaction nets → strong confluence: locality + one rule per pair ⇒ one-step confluence.
    • Interaction nets ↔ textual calculi: wiring ↔ name-multiplicity + equations.
    • Textual calculi ↔ implementation: indirections/subst cells model pointer updates.
    • Implementation ↔ scheduler: correctness depends on atomicity, non-overlap, readback assumptions.
    • IC (HOC) ↔ nets: affine vars + dup/sup/labels; operationally net-like rewrites.
    • IC ↔ readback: quoting/collapse needed for λ-term output.
    • MOV vs DUP ↔ semantics+perf: MOV reduces interactions but needs invariants (linearity, branch separation, labels, substitution correctness).
    • HVM4 parser/desugaring → IC shape: cloned binders insert auto-dups; label freshness matters.
    • Dynamic labels → discipline: equality/commutation depends on computed labels.
    • Bend → HVM2: compiler inserts dups/erasures; “sharing” becomes concrete DUPs.
    • HVM2 interaction table → implementation: link/call are non-local fast cloning.
    • Collapser queue discipline → output order: key BFS can reorder branches.
Optional DOT/Graphviz
digraph IN_KG {
  rankdir=LR;
  Lambda -> SharingGraphs [label="graph reduction"];
  SharingGraphs -> DupErase [label="explicit control"];
  DupErase -> Optimality [label="cost model"];
  Optimality -> Lamping [label="mechanisms"];
  LinearLogic -> ProofNets -> InteractionNets;
  InteractionNets -> StrongConfluence;
  InteractionNets -> TextualCalculi [label="encodings"];
  TextualCalculi -> Indirections [label="explicit subs/cells"];
  Indirections -> Implementation;
  Implementation -> Scheduler;
  Scheduler -> Parallelism [label="hazards"];
  InteractionCombinators -> InteractionNets [label="universal basis"];
  HOC_IC -> InteractionNets [label="operational correspondence"];
  HOC_IC -> Readback [label="quoting/collapse"];
  Readback -> ObservationalEq;
  MOV -> HOC_IC [label="optimization node"];
  MOV -> ObservationalEq [label="needs proof/testing"];
  DUP -> HOC_IC;
}

2) Interaction Nets — crisp theory
2.1 Core definitions
Signature & agents
    • Signature Σ: symbols α with arity ar(α)=n.
    • Agent occurrence: node α with n aux ports + 1 principal.
Ports/wiring/nets
    • Net: undirected graph; each port degree=1; free ports = interface.
    • Diagrams: principal marked; aux ports numbered.
Active pair
    • Active pair = principal–principal; only rewrite site.
Interaction rules/systems
    • Rule (α,β) ⇒ N (fixed RHS) with same interface.
    • Constraints: one rule per unordered pair; local + interface-preserving (bijective free ports).
Port ordering & interface discipline
    • Rule diagram must specify aux order; “left/right child” meaningless without numbering.
    • Textual α(t1..tn) fixes order (ti ↔ aux i).
    • If LHS↔RHS free-port bijection is unclear, the rule is underspecified.
Reduction
    • Replace active pair with RHS; reconnect via interface.
2.2 Strong confluence / one-step diamond
    • Two disjoint active pairs reduce ⇒ results join in one step (uniform/strong confluence).
Guarantees (if terminating):
    • Unique normal form (up to net equivalence).
    • Strategy-independent result.
Not guaranteed:
    • Termination; cost invariance; deterministic readback order.
    • Requires “one rule per unordered pair”; extra nodes/partial coverage can break assumptions.
2.3 Locality & O(1) rule application assumptions
    • RHS size fixed; rewiring touches O(1) ports; alloc/free via bump/freelist.
    • Reality: bookkeeping (GC, active-pair discovery, indirections) can dominate; optimal reduction adds admin nodes.
2.4 Manual reduction discipline (pitfall-resistant)
    1. Label ports on active pair: α0/α1..αn, β0/β1..βm.
    2. Record external wiring for each aux port.
    3. Replace with RHS whose interface matches α1..αn, β1..βm.
    4. Reconnect by bijection (each external link exactly once).
    5. Sanity: no dangling/double links; interface multiset unchanged.
    • If port correspondence is ambiguous, you’re missing a spec detail.
2.5 Quick net invariant checklist
    • Port degree=1; no self-links unless allowed.
    • Active pairs are principal–principal only.
    • Interface preserved bijectively.
    • RHS net size fixed per rule; no ad-hoc allocation.
    • Labels/metadata exactly per rule; no implicit freshening.
    • Fresh names occur exactly twice.

3) Interaction calculus — textual semantics (FM + lightweight)
Textual calculi for nets (not HVM4 IC surface).
3.1 Key trick: “names are wires” + multiplicity
    • Each name occurs ≤2 times (often exactly twice inside rules; free names once).
    • Textual analogue of “wire connects exactly two ports.”

Multiplicity triage (do not auto-infer ERA)
Name-count diagnostics depend on what is supposed to be closed vs what is interface:

For textual nets (FM/lightweight):
- 2 occurrences: internal wire (good).
- 1 occurrence: either (a) interface/free wire (good) OR (b) dangling port in a supposedly closed region (bug).
- 0 occurrences: name unused (usually indicates it should not exist; may arise from dead code elimination or malformed construction).
- >2 occurrences: illegal fan-out unless an explicit duplicator mechanism exists in the calculus you’re using.

For HVM4 IC (affine-by-default):
- 0 or 1 use of a regular variable is legal (affine).
- >1 use requires explicit DUP/SUP (possibly inserted by parser auto-dup) or a MOV-based transformation with proven side-conditions.
- “Missing ERA” is not inferred from “occurs once”; erasure is about intentionally discarding an argument/value in a setting that otherwise forces consumption.

Debug rule:
- If you see a single occurrence where you expected a closed internal wire, first decide: “Is this intended to be interface?” If not, treat it as dangling wiring, not automatically as ‘insert ERA’.

3.2 Typical syntax (lightweight/FM)
    • Agents Σ with arity; names N={x,y,z,...}.
    • Terms t ::= x | α(t1..tn), names ≤2 uses; optional indirection $t.
    • Equations: unordered t = u.
    • Rules: α(x̄)=β(ȳ) ⇒ Δ with all names exactly twice.
    • Configurations: ⟨t̄ | Δ⟩ (head terms + equation multiset).
3.3 Operational steps (interaction vs admin)
    • Communication: resolve shared names (x=t, x=s).
    • Substitution: propagate term into name occurrence (often via indirections).
    • Collect: move resolved bindings into head/interface.
    • Interaction: α(...) = β(...) ⇒ RHS Δ with fresh names + parameter subst.
    • Insight: implementations can reduce with mostly interaction+communication; substitution/collect via indirections.
3.3b Linking is the only non-local step
    • Resolving x=t and x=u forces a global substitution on the other occurrence.
    • Operationally non-local; in HVM2 this is LINK.
3.4 Deadlocks/cycles (careful)
    • Normal form: no active pair (no principal–principal equation).
    • Can be stuck without being a “final value” (missing rules, malformed encoding, suspended computation).
    • Cycles can encode recursion or indicate bugs (dangling subs/self-referential indirections).
    • Indirection cycles can cause infinite pointer-chasing/readback nontermination.
    • HVM2 forbids “vicious circles”; frontends should enforce.
3.5 Net ↔ configuration mapping
Net → configuration
    1. Choose interface free ports (head terms or free names).
    2. For each agent α: build α(t1..tn), fresh names as needed.
    3. For each principal–principal connection, add equation t = u.
    4. Check name multiplicity (≤2).
Configuration → net
    1. Build term trees α(t1..tn).
    2. Each equation connects roots’ principal ports.
    3. Names appearing twice become wires; once = free port.
HVM2 textual nets
    • Root tree + list of redexes (root ~ root) via named vars.
    • Typically one free main port; extra free ports via extra redexes.
3.6 Name-discipline debug checklist
    • Name 3+ times → missing DUP (or desugaring under-duplicated).
    • Name once where internal wiring expected → missing ERA.
    • Name twice in unrelated subterms → wiring/port mismatch.
    • Substitution cycles: prefer explicit indirection cells + cycle checks.

4) λ-calculus connections (sharing/dup/erase only)
4.1 Sharing operationally
    • Example term: (λx. t[x,x]) u.
    • Tree substitution duplicates u; graph reduction shares u and duplicates only when needed.
    • Track: when to duplicate; what to erase when unreachable.
4.2 Why dup/erase are hard
    1. Correctness: too-early copy changes sharing/cost; too-late copy can change termination/observations (incl. readback).
    2. Graph invariant: ports degree=1; “use x twice” requires explicit split.
    3. Optimality: avoid duplicating the same residual redex.
Linear-logic intuition
    • DUP ≈ contraction; ERA ≈ weakening.
    • Name occurs 0× where value expected → ERA; 2+× → DUP.
4.3 Micro-examples
Example A: (λx. x+x) (expensive()) → shared cost ~1 vs duplicated cost ~2; net must encode via DUP or compiler sharing.
Example B: (λx. 0) (diverges()) → strict tree substitution diverges; lazy sharing + ERA can terminate.
4.4 “Optimal” intuition (only)
    • Lévy optimal: never duplicate same residual redex.
    • Lamping-style: fans/annotations for controlled duplication.
    • Interaction nets give local rewrites; optimality has big constants/invariants.
Failure modes
    • Confluence ≠ optimality.
    • Optimality ≠ practical speed for all workloads.
    • “Sharing” can be altered by readback/collapse order; define observation.

5) Implementation playbook (crucial)
For building/debugging evaluators/compilers.
5.1 Data structure options for nets
Option 1: Explicit ports + wires (graph-centric)
    • Node struct holds:
        ◦ tag (agent symbol)
        ◦ arity
        ◦ array of port endpoints (indices to “wire objects”)
    • Wire object connects exactly two endpoints (or one endpoint + “free”).
Pros: direct; easy degree=1 checks. Cons: overhead/indirections/slower.
Option 2: Half-edge / port-pointer (pointer-centric)
    • Each port stores a pointer (or packed word) to the port it’s connected to.
    • Wires are implicit: a wire is just the symmetric pointer pair.
Pros: fast rewiring; minimal allocs. Cons: easy invariant breakage; must keep symmetry.
Option 3: “Name occurs twice” mapping (textual-calculus)
    • Represent each name as a slot that stores up to two endpoints.
    • Use union-find / substitution cells to redirect names during reduction.
Pros: maps to textual calculi; easy substitution reasoning. Cons: cycles/path compression hazards.
Option 4: Implicit principal port (interaction-combinator)
    • Main/principal port is not stored explicitly; a node only stores its two auxiliary ports.
    • Redexes are written as root~root; “main” connectivity is implicit.
Pros: compact (e.g., 2×32-bit ports in 64-bit word); good for atomic updates.
Cons: less direct for arbitrary signatures; harder varying arity without extra tagging.
5.2 Wires + invariants
Debug invariants
    • Port degree=1 (or FREE sentinel).
    • Symmetry: p.link=q ⇒ q.link=p.
    • Arity correctness: tag ⇒ port count; bounds OK.
    • Interface preservation: only active pair rewritten; external links bijective.
Debug checks
    • check_net(): valid tag range, ports in range, symmetric links, no self-links (unless allowed), no dangling pointers.
    • check_name_multiplicity(): names have 0/1/2 occurrences (internal vs free).
5.3 Active-pair discovery & scheduling
Sequential
    • Keep stack/queue of candidate active pairs.
    • Rewrites affect only nearby links → push neighbors; avoid O(N) rescans.
Parallel hazards
    • Prevent overlapping reductions, half-updated reads, ABA on reused IDs.
Mechanisms
    • Per-node locks; or lock-free CAS + ownership; or disjoint work-stealing deques.
    • Rule: correctness first; graph-rewrite races silently corrupt.
HVM2 pattern
    • Overlap via shared vars; atomic link + substitution map defers until both ends appear.
    • Global redex bag; reducer must own both nodes it rewires.
5.4 Rule compilation (pattern → RHS → reconnect → retire)
Repeatable rewrite outline:
    1. Match: confirm you have an active pair with tags (α,β) and port pointers for each aux port.
    2. Snapshot external links (the interface of the redex).
    3. Allocate RHS nodes (or reuse from freelist).
    4. Wire RHS internally (local).
    5. Reconnect external links to RHS interface ports.
    6. Retire LHS nodes (free/reuse), but only after all pointers are detached.
C-like pseudocode skeleton:
typedef struct { uint32_t tag; uint32_t arity; Port ports[MAX_ARITY+1]; } Node;

void rewrite(Node* a, Node* b) {
  assert(is_active_pair(a,b));
  ExtLinks ext = snapshot_aux_links(a,b);
  RHS rhs = build_rhs(a->tag, b->tag);
  connect_rhs(rhs);
  reconnect(ext, rhs);
  retire(a); retire(b);
}
5.5 Indirection/substitution bugs + instrumentation
Indirections avoid global substitution. Bug classes:
    • Lost update: you update one side of a wire but not the symmetric pointer.
    • Dangling redirect: indirection points to freed node.
    • Redirect cycle: x → y → x causes infinite chasing.
    • Stale reads in parallel: a thread sees an intermediate state.
Instrumentation:
    • Count pointer-chasing steps; abort if > threshold (cycle suspicion).
    • Log every creation of indirection/substitution cell with “from, to, reason, rule-id”.
    • Add an optional “coloring”/epoch field to nodes to detect use-after-free.
5.6 Correctness invariants (debug)
Minimal set:
    • assert(active_pair_principal_principal(a,b)) before rewrite.
    • After rewrite:
        ◦ all ports touched satisfy symmetry.
        ◦ LHS nodes are unreachable from interface (or marked retired and never dereferenced).
    • For name-based representations:
        ◦ name occurrences remain within allowed multiplicity.
    • For labeled dup/sup:
        ◦ labels in RHS are exactly as rule specifies; never “invent” labels.
5.7 HVM2-specific implementation notes (interaction combinators)
    • Main port is implicit; a node stores only two auxiliary ports, enabling compact 64-bit nodes.
    • Wires can be stored as atomic words; interactions can be implemented lock-free with CAS.
    • LINK (name substitution) is the only non-local update; treat it as a global wire rewiring.
    • REF nodes act like fast function pointers: CALL expands a static definition without incremental duplication.
    • Port layout (paper): 32-bit port = 3-bit tag + 29-bit value; nodes are just two ports (64-bit).
    • Ports store the tag of the connected node; nodes themselves are typeless pairs.
    • Global net uses node buffer + vars substitution map + redex bag (all atomic in parallel runtime).
    • Substitution map lets LINK defer until second occurrence; must be atomic to avoid races.
    • Link algorithm (paper): if A is VAR, atomic_exchange subst[A] with B; if empty, stop; if not, delete entry and link the previous value with B (repeat).
    • DUP-REF copy optimization is guarded by a “safe” flag (def has no DUPs); unsafe refs must be expanded, or treated as UB in frontends.
    • Safety propagation is only for global defs; local unsafe code can still be duplicated and produce surprising ERA placements.
5.8 HVM4-specific memory/term layout notes (Interaction Calculus)
    • Term pointer layout is SUB|TAG|EXT|VAL; linked vars (VAR/DP0/DP1/GOT) point to binder slots.
    • SUB cells are in-place redirections; every linked occurrence must read through the SUB bit.
    • Distinguish binder terms (DUP/MOV as [expr, body]) from binder nodes (shared expr slot for DP0/DP1/GOT).
    • ALO terms lazily instantiate static (book) terms into dynamic heap terms.
    • SUB bit is ignored for immediates; TAG determines interpretation of EXT/VAL.
5.9 Performance instrumentation (meaningful)
Separate counters:
    • Interactions: number of rule firings at active pairs.
    • Administrative work: indirection traversals, substitution/collect operations, GC steps.
    • Alloc/free: node allocations, freelist hits/misses.
    • Scheduler overhead: work-steal attempts, contention, failed CAS, lock waits.
Avoid misleading metrics:
    • “Fewer interactions” can still be slower if each interaction becomes heavier.
    • “Fewer allocations” can still be slower if you increase pointer chasing.
For optimization claims, demand:
    • A baseline and a variant with identical semantics and readback settings.
    • The same output under differential testing.

6) HVM/HVM4 orientation (practical semantics crib)
HVM4 surface/core → net-like rewriting (operational view).
6.1 HVM4 in one line
HVM4: affine Interaction Calculus runtime with explicit DUP/SUP; eval then optional CNF collapse to ordinary λ-terms/values.
6.2 HVM4 core terms + syntax gotchas
Core terms (docs/hvm4/core.md):
    • Variables: x (VAR), x₀/x₁ (DP0/DP1), mov-bound GOT x, quoted vars BJV/BJ0/BJ1/BJM.
    • Binders/structure: Lam, App, Dup, Sup, Mov, Era (&{}), Ctr #Name{...}, Mat λ{#C:..}, Swi λ{N:..}, Use λ{t}.
    • Extras: Num, Op2, Eql, And/Or, Red (~>), Inc (↑), Ref @name, Nam ^name, Dry ^(f x), Any *, Alo @{...}, Uns !${...}.
    • Dynamic labels: DSu &(...){a,b}, DDu !x&(lab)=v; body.
Parser/desugaring traps (docs/hvm4/syntax.md):
    • No whitespace application: use f(a,b); postfix call binds tightest.
    • Cloned binders (&x) and inline dup on lambda/let insert nested DUPs with fresh labels.
    • let sugar (!x = v; body) desugars to application; strict let (!!) is different.
    • Fork sugar &Lλx,y{A;B} injects dup vars and label; branch side selection can be implicit.
    • Variables are global wires (scopeless); occurrences can appear outside lexical regions.
6.3 Core IC interactions (the actual four)
    • APP-LAM: (λx.f a)  → x ← a; f
    • APP-SUP: (&L{f,g} a) → !A &L= a; &L{(f A₀),(g A₁)}
    • DUP-LAM: !F &L= λx.f
        → F₀ ← λ$x0.G₀; F₁ ← λ$x1.G₁; x ← &L{$x0,$x1}; !G &L= f
    • DUP-SUP: !X &L= &R{a,b}
        → if L==R then X₀←a; X₁←b; else !A &L= a; !B &L= b; X₀←&R{A₀,B₀}; X₁←&R{A₁,B₁}
Treat these as the “physics.” Everything else (numbers, matches, ops, readback) is engineering around them.
6.4 MOV propagation rules (HVM4)
    • MOV-LAM/MOV-SUP/MOV-NOD/MOV-DRY/MOV-NAM/MOV-RED/MOV-MOV push a MOV binder through structure.
    • MOV has no labels; it is a sharing optimization that relies on branch separation invariants.
    • When debugging, check MOV rewrites first: they are easy to mis-implement and hard to observe.
6.5 HVM4 memory + rewriting model (the facts you need to debug low-level issues)
    • Term pointer layout: SUB|TAG|EXT|VAL (64-bit). Labels and levels live in EXT; heap locations in VAL.
    • Linked vars (VAR/DP0/DP1/GOT) point to binder slots; those slots become SUB cells after interaction.
    • Distinguish binder terms (DUP/MOV as [expr, body]) from binder nodes (shared expr slots for DP0/DP1/GOT).
    • ALO lazily instantiates static book terms into dynamic heap terms (static vs dynamic split is real).
6.6 Collapser/CNF readback: how to interpret HVM4 outputs
    • cnf reduces to WNF, then lifts the first SUP to the top and returns immediately.
    • ERA propagates upward; RED keeps only its RHS; INC adjusts collapse priority.
    • eval_collapse enumerates branches via a work-stealing key queue; SUP increases key, INC decreases key.
    • FIFO within a key bucket when single-threaded; parallel runs can reorder across buckets.
Label behavior recap:
    • Same-label SUPs annihilate pairwise.
    • Different-label SUPs commute (cross product of branches).
Operational gotchas:
    • Output may be a stream of λ-terms, not a single term.
    • Branch order is a readback artifact; parallel runs may reorder.
6.7 HVM4 control/extended node families (high-level behavior)
RED (~>) guarded reduction
    • APP-RED rules push application through the RHS when it is a lambda/sup/use/red/mat.
    • If RHS is a constructor/name/dry, APP-RED yields a dry application ^((f ~> rhs) a).
    • If RHS is &{}, APP-RED returns &{}; if RHS is ↑g, APP-RED lifts ↑.
    • Collapser keeps only the RHS, so RED changes evaluation order and readback behavior.
USE (λ{f}) unbox/force
    • (λ{f} x) → (f x); distributes over SUP; ERA erases; INC lifts priority.
INC (↑) priority wrapper
    • Propagates outward through APP/USE/OP2/MAT/EQL/AND/OR; affects collapse queue order.
DRY and NAM (stuck heads)
    • ^name and ^(f x) represent non-reducible heads; used to preserve stuckness.

Stuckness contract (stuck vs error vs normal form)
Do not call something an “error” unless the current evaluator/spec explicitly treats it as such.

Definitions:
- Normal form (net): no active pairs.
- Stuck term (language observation): a term that is not reducible under the system’s rules but is still a meaningful observable (often represented explicitly as a “dry application” or “name head” form).
- Runtime error: an implementation-defined failure state (e.g., applying a numeric literal as a function), which may differ across versions.

Policy:
- If rule docs describe a case as producing a DRY/NAM/stuck form, treat it as “stuck,” not “error.”
- If you are unsure whether a case is stuck or error in the current runtime, mark VERIFY and point to the exact place to check (rule doc vs evaluator dispatch).
- Keep one authoritative statement of each behavior and reference it elsewhere to avoid contradictions.

ANY (*)
    • Structural equality treats * as matching anything (EQL-ANY yields #1).
EQL (structural equality)
    • EQL-LAM uses a fresh name to compare bodies; EQL-CTR compares tags then fields.
    • For SUC/CON, comparisons are chained with INC to control collapse order.
    • Distributes over SUP; INC lifts; EQL-ANY returns #1.
AND/OR (short-circuit)
    • #0 is false; non-zero is true. AND returns b when true; OR returns #1 when true.
    • SUP distributes; ERA erases.
OP2 (binary ops)
    • NUM op NUM evaluates; op distributes over SUP; ERA erases; INC lifts.
MAT (pattern match)
    • App-mat dispatches on constructor; mismatch takes miss branch.
    • MAT distributes over SUP; INC lifts priority.
ALO (allocation / instantiation)
    • @{s} t threads a substitution list over a static term; LAM/DUP/MOV freshen names.
    • VAR/GOT/DP0/DP1 consult the substitution list or fall back to de Bruijn level.
DUP propagation beyond SUP/LAM
    • DUP-NOD duplicates constructors/tuples by duplicating each field.
    • DUP-NAM duplicates stuck names.
    • DUP-DRY duplicates stuck applications by duplicating head and arg.
    • DUP-RED duplicates guarded reductions componentwise.
APP to non-lambda heads
    • APP-CTR/NAM/DRY produce a stuck dry app ^(head arg).
    • APP-ERA erases; APP-INC lifts priority wrapper.
Dynamic labels (DSU/DDU)
    • DDU-NUM turns a computed label into a static label; DDU-ERA erases; DDU-INC lifts.
    • DDU-SUP splits the dynamic label into per-branch labels and distributes v/body accordingly.
    • DSU-SUP distributes a dynamic label over a SUP; DSU-ERA erases; DSU-INC lifts.
UNS (unscoped binding)
    • !${f,v}; t expands to t(λy.λ$x.y, $x) (helper for scopeless lambdas).

6.8 Reading HVM4 programs for “sharing vs duplication” intent
    • !x&L = v; ... x₀ ... x₁ ... means explicit duplication with label L.
    • %x = v; ... x ... x ... means “move/share” without duplication (semantics-sensitive).
    • Dynamic labels (!(lab) / &(...)) mean label equality is computed, not syntactic.
6.9 Scopeless lambdas (Bend/HVM) — what they imply
    • $x binds globally within a term; $x can appear outside the lambda body.
    • If a scopeless lambda is erased, its bound var becomes * (ERA).
    • Duplicating a scopeless lambda yields a SUP of its arguments; ordering is compiler-chosen.
    • Scopeless variables do not cross top-level definitions (each term has its own binding scope).
6.10 HVM2 orientation (interaction combinators, not IC)
    • Core nodes: ERA/CON/DUP plus REF/NUM/OPR/MAT extensions; VAR represents wires (matches compile to these).
    • Principal ports are implicit; a node stores only two auxiliary ports (compact 64-bit nodes).
    • Ports store the tag of the node they point to; nodes are just pairs of ports.
    • Wires are atomic variables; interactions can be lock-free with CAS.
    • Key interactions: LINK (name substitution), CALL (expand REF), VOID, ERASE, COMMUTE, ANNIHILATE, OPERATE, SWITCH.
    • REF enables fast global defs and constant-space tail calls; ERA on REF/NUM behaves like copy.
    • If a REF definition is marked unsafe (contains DUP), duplicating it must expand/call (or be rejected).
    • Bend compilation/readback uses port polarity: CON is lambda vs application depending on entry port; DUP is dup vs sup likewise.
    • NUM payload (paper): 29-bit value with 5-bit subtag + 24-bit data (U24/I24/F24 or operator tag).
    • HVM2 assumes no “vicious circles” (self-referential nets); enforce this in frontends.
    • Defs include an explicit root port and a “safe” flag; names are indices into the global book.
6.11 HVM2 vs HVM4 crosswalk (fast disambiguation)
    • Core model: HVM2 = interaction combinators; HVM4 = Interaction Calculus with explicit DUP/SUP labels.
    • Principal port: HVM2 implicit; HVM4 explicit in term structure.
    • Labels: HVM2 has no DUP/SUP labels; HVM4 labels drive annihilation vs commutation.
    • Readback: HVM2 prints via combinator polarity + encoding; HVM4 collapses via CNF (SUP lifting).
    • Substitution: HVM2 LINK is a named-wire substitution; HVM4 uses SUB cells in heap slots.
6.12 Bend strictness + laziness gotchas (practical)
    • HVM2 is strict; naïve recursion can unfold forever if the recursive call is in an active position.
    • Bend’s float-combinators pass lifts closed lambdas to top-level defs, turning them into lazy REFs.
    • “Make recursion lazy” by ensuring the recursive step is inside a combinator that can be lifted.
    • Linearization (auto-dup) can change evaluation order; keep one source of duplication.
    • Rule of thumb for fusion: push linear lambdas upward, duplicating lambdas downward.
    • Useless duplications in recursive code can cause nontermination under strict evaluation.
    • Fusing functions: share arguments across branches to avoid duplicating data that only one branch uses.
    • linearize-matches runs before manual `with`; it should not duplicate already-linearized vars.
6.13 HVM4 runtime mechanics (clang evaluator notes)
WNF engine shape
    • WNF uses an explicit stack (no recursion): enter phase descends into head/strict position, apply phase pops frames to dispatch interactions.
    • Frames include APP/OP2/EQL/AND/OR/DSU/DDU plus specialized frames for RED/MAT/USE.
    • DP0/DP1 and GOT evaluate the shared expr slot, then dispatch DUP/MOV rules; they do not interact with APP.
    • REF reduces to ALO when a book entry exists; ALO instantiates static terms on demand.
Apply-phase dispatch table (condensed, ASCII)
```
APP frame ([ ] x):
  ERA -> APP-ERA; NAM/VAR/BJV/BJM/BJ0/BJ1 -> APP-NAM; DRY -> APP-DRY; LAM -> APP-LAM (enter)
  SUP -> APP-SUP; INC -> APP-INC; MAT/SWI/USE -> push frame, eval arg; RED -> push F_APP_RED, eval g
  CTR -> APP-CTR (stuck); NUM -> runtime error; default -> rebuild APP

F_APP_RED ((f ~> [ ]) x):
  ERA -> APP-RED-ERA; SUP -> APP-RED-SUP; INC -> APP-RED-INC; LAM -> APP-RED-LAM; RED -> APP-RED-RED
  MAT/SWI -> push F_RED_MAT, eval arg; USE -> push F_RED_USE, eval arg
  NAM/BJ* -> APP-RED-NAM; DRY -> APP-RED-DRY; CTR -> APP-RED-CTR; default -> rebuild (f ~> g) x

MAT/SWI (mat [ ]):
  ERA -> APP-ERA; SUP -> APP-MAT-SUP; INC -> MAT-INC; CTR -> APP-MAT-CTR (enter)
  NUM -> match ext vs val; enter h or (m num); RED -> drop g, eval (mat h)
  NAM/BJ*/DRY -> DRY; default -> rebuild APP

F_RED_MAT ((f ~> mat) [ ]):
  ERA -> APP-RED-MAT-ERA; SUP -> APP-RED-MAT-SUP; INC -> APP-RED-MAT-INC
  CTR -> APP-RED-MAT-CTR (match/miss); NUM -> APP-RED-MAT-NUM (match/miss)
  RED -> drop g, keep frame; default -> DRY

USE (use [ ]):
  ERA -> USE-ERA; SUP -> USE-SUP; INC -> USE-INC; RED -> drop g, eval (use h)
  default -> USE-VAL (enter)

F_RED_USE ((f ~> use) [ ]):
  ERA -> APP-RED-USE-ERA; SUP -> APP-RED-USE-SUP; INC -> APP-RED-USE-INC
  RED -> drop g, keep frame; NAM/BJ*/DRY -> DRY; default -> APP-RED-USE-VAL

OP2 ([ ] op y):
  ERA -> OP2-ERA; NUM -> if y NUM then OP2-NUM-NUM else push F_OP2_NUM, eval y
  SUP -> OP2-SUP; INC -> OP2-INC-X; default -> rebuild OP2

F_OP2_NUM (x op [ ]):
  ERA -> OP2-NUM-ERA; NUM -> OP2-NUM-NUM; SUP -> OP2-NUM-SUP; RED -> drop g, eval (x op h)
  INC -> OP2-INC-Y; default -> rebuild OP2

EQL ([ ] === b):
  ERA -> EQL-ERA-L; ANY -> EQL-ANY-L; SUP -> EQL-SUP-L; INC -> EQL-INC-L
  default -> store a, push F_EQL_R, eval b

F_EQL_R (a === [ ]):
  ERA -> EQL-ERA-R; ANY -> EQL-ANY-R; SUP -> EQL-SUP-R; INC -> EQL-INC-R
  NUM/LAM/CTR/MAT/SWI/USE/NAM/DRY -> corresponding EQL-*; default -> #0

DSU (&( [ ]){a,b}):
  ERA -> DSU-ERA; NUM -> DSU-NUM; SUP -> DSU-SUP; INC -> DSU-INC; default -> rebuild DSU

DDU (!x&( [ ])=v; b):
  ERA -> DDU-ERA; NUM -> DDU-NUM (enter); SUP -> DDU-SUP; INC -> DDU-INC; default -> rebuild DDU

AND ([ ] .&. b):
  ERA -> AND-ERA; SUP -> AND-SUP; INC -> AND-INC; NUM -> AND-NUM (enter); default -> rebuild AND

OR ([ ] .|. b):
  ERA -> OR-ERA; SUP -> OR-SUP; INC -> OR-INC; NUM -> OR-NUM (enter); default -> rebuild OR

DP0/DP1 (dup expr):
  NAM/BJ* -> DUP-NAM; DRY -> DUP-DRY; RED -> DUP-RED; LAM -> DUP-LAM; SUP -> DUP-SUP (enter)
  ERA/ANY/NUM/MAT/SWI/USE/INC/OP2/DSU/DDU/CTR -> DUP-NOD (may enter)
  default -> allocate expr slot, return DP0/DP1

GOT (mov expr):
  GOT -> MOV-MOV (enter); NAM/BJ* -> MOV-NAM; DRY -> MOV-DRY; RED -> MOV-RED; LAM -> MOV-LAM
  SUP -> MOV-SUP (enter); ERA/ANY/NUM/MAT/SWI/USE/INC/OP2/DSU/DDU/CTR -> MOV-NOD (may enter)
  default -> allocate expr slot, return GOT
```
Substitution cells
    • heap_subst_var(loc, val) stores val with SUB bit set; all linked vars must read through SUB.
    • heap_subst_cop(side, loc, r0, r1) stores the opposite branch in the slot and returns the selected branch.
DUP/MOV fallback behavior
    • If a DUP/MOV encounters an unhandled tag, the runtime allocates a new expr slot and rewires DP0/DP1 or GOT to preserve linearity.
Runtime stuckness
    • APP to constructors/names/dry heads is *stuck*, represented as a dry application:
        ◦ APP-CTR: (ctr a) → ^(ctr a)
        ◦ APP-NAM / APP-DRY similarly preserve stuckness by producing/extending ^(head arg).
    • APP of NUM is not a valid function application; whether this is treated as an error vs a stuck form is an implementation choice — VERIFY in the current evaluator if you want to rely on it.
    • Erasing lambdas (LAM_ERA_MASK) shortcut APP-LAM: returns body without substituting.
CNF implementation details (clang/cnf/_.c)
    • cnf reduces to WNF then lifts only the first SUP found; other SUPs stay inside branches.
    • cnf output invariant: either SUP/ERA/INC at root, or no SUP/ERA/INC anywhere in the term.
    • If any child collapses to ERA, cnf returns ERA for the whole node.
    • For LAM: binder is quoted to BJV; if body collapses to SUP, cnf returns SUP of two lambdas.
    • cnf_inj applies a template to args; if the head arg is SUP, it clones template + remaining args.

7) MOV vs DUP debugging template (NO SOLUTION)
Goal: repeatable test/debug of MOV≡DUP claims + interaction savings.
7.1 Define equivalence (pick target)
    1. CNF readback equivalence: same CNF stream/multiset up to α-renaming + allowed branch reorder.
    2. Graph normal-form equivalence: isomorphic normal forms (pointer identity irrelevant).
    3. Contextual/observational equivalence: no context distinguishes (hard; approximate via tests).
Be explicit: branch order? labels observable? erased values (&{}, *) observable?
7.2 Differential testing (fast)
    1. Normalize runtime: same flags/collapse/threads/output limit.
    2. Run both encodings; capture full output (or high enough limit).
    3. Normalize outputs: α-normalize; canonicalize branch order if allowed.
    4. Compare; on mismatch → trace.
7.3 Trace comparison
A) Rule-fire sequences (high signal): log active-pair tags+labels, LHS IDs, substitutions, interface ports; stop at first divergence (rule position, subst content, label mismatch).
B) Frontier-shape hash: multiset of tags/labels, SUB count, pending SUP count → detect silent drift.
C) Readback-only: compare raw-net dumps pre-collapse; if equal, bug is readback/collapse.
7.4 Plausible root causes
Spec mismatch
    • MOV not equivalent to DUP in all contexts; may require branch separation.
    • Labels commute vs annihilate; outputs differ if you assumed pairwise alignment.
    • Auto-dup adds labels/DUP nodes you didn’t count.
    • Bend “dup of dup” interference: duplicating a duplicating function can be semantically invalid.
Implementation bug
    • Wrong MOV rules/coverage; wrong reconnection; bad SUB propagation; node/term confusion; asymmetric rewiring; use-after-free.
Eval-order assumption
    • Optimization changes SUP lifting / DUP forcing; CNF output can change under same underlying net.
Printer/collapse artifact
    • Same net, different collapse traversal/key-queue order/limit.
7.5 Debug checklist
Step 0: minimize reproducer (single MOV + DUP, single output diff, interaction-count diff).
Step 1: fix observation (CNF multiset vs raw net vs scalar).
Step 2: instrument: active pair tag pair, labels, LHS IDs, substitutions, alloc/reuse events.
Step 3: assert invariants at divergence (symmetry, valid SUB targets, no SUB cycles, label-branch choice, interface preserved).
Step 4: locate bug: early net divergence → evaluator/rules; net same but CNF differs → collapser; perf differs → scheduler.
Step 5: only optimize after equivalence is proven.

8) LLM failure modes + countermeasures
8.1 Traps
    1. Term vs graph rewriting confusion → implicit copy hallucinations.
    2. Port identity loss → “left/right child” without port numbering.
    3. α-conversion handwaving → mixing λ renaming with name/wire multiplicity.
    4. Invented rules (esp. MOV/extended nodes).
    5. Assuming lexical scope (scopeless vars violate this).
    6. Conflating eval with readback (collapse order ≠ semantics).
    7. Performance myths: fewer interactions ≠ faster; ignore alloc/subst costs.
    8. Partial-rule coverage ignored → stuck normal forms.
    9. HVM2/HVM4 conflation → bogus reductions.
    10. Ignoring desugaring (auto-dup/fork/no-whitespace application).
    11. Misreading dynamic labels (runtime equality).
    12. Assuming lazy eval in HVM2/Bend (strict recursion can diverge unless floated).
    13. Ignoring REF safety in HVM2 (unsafe duplication).
8.2 Countermeasures
    • Confirm node signatures, rule set, observation function.
    • Use reduction worksheet; track wiring explicitly.
    • Equivalence only with proof sketch or differential tests.
    • Treat MOV as “conditional” until proven.
    • Debug desugared core term; labels/DUPs often appear only after parsing.
    • Keep HVM2 vs HVM4 assumptions explicit.
    • For Bend/HVM2, confirm recursion is guarded by REFs (float-combinators).
    • When cloning REFs in HVM2, check def.safe (or default to unsafe).

9) Quick-reference appendix
9.1 Glossary (minimal, operational)
    • Arity: number of auxiliary ports.
    • Principal port: distinguished port defining active pairs.
    • Auxiliary ports: non-principal; wire args/fields.
    • Active pair: principal–principal edge; only rewrite site.
    • Interface: free ports (observable boundary).
    • Indirection/SUB cell: explicit redirection to avoid global substitution.
    • DUP: explicit split producing two correlated projections.
    • SUP: explicit branching; distributes interactions.
    • Label: controls DUP/SUP annihilation vs commutation.
    • Quoted vs linked vars: readback indices vs runtime pointers.
    • CNF/collapse: enumerate branches; print ordinary λ-terms/values.
9.2 Minimal rule schema templates (fill with your system’s specifics)
Interaction net rule template (graph)
    • LHS: α connected to β at principal ports.
    • Interface ports: α1..αn, β1..βm.
    • RHS: fixed net N with exactly n+m free ports; provide a bijection mapping to the LHS interface.
Textual calculus rule template (equational)
    • α(x̄) = β(ȳ) ⇒ Δ(x̄,ȳ)
    • Freshen bound names in Δ on each use (capture-avoidance at the wire-name level).
Label-sensitive duplication template (conceptual)
    • If labels equal: pairwise projection / annihilation.
    • If labels differ: commuting rewrite producing cross product structure.
9.3 Reduction-by-hand worksheet (tiny form)
Use for a single rewrite:
    1. Active pair: agents α(ar=n), β(ar=m); principal α0—β0.
    2. External links: α1..αn ↔ ?, β1..βm ↔ ?.
    3. Rule used: (α,β) ⇒ RHS pattern id.
    4. RHS construction: new nodes, internal wiring, RHS interface map.
    5. Reconnect: map (α1..αn, β1..βm) → RHS free ports; verify interface preserved.
    6. Post-check: degree=1 per port; no dangling; label/name constraints satisfied.
9.4 Implementation checklist (debug session)
    • Fix observation: raw net vs CNF output; define allowed reordering.
    • Run single-threaded deterministic mode (if available) before parallel.
    • Add check_net() after every N rewrites (start with N=1 for tiny repro).
    • Log every substitution/indirection creation; detect cycles.
    • Validate rule coverage: every active pair encountered has an implemented rule.
    • Validate node/term distinction (binder term vs shared node) for dup/mov-like constructs.
    • Measure separately: interactions, pointer chasing, allocations, queue contention.
    • Only optimize after semantic equivalence is established.
9.5 HVM4 term-pointer cheat sheet (debugging)
    • Layout: SUB|TAG|EXT|VAL (64-bit; 1/7/24/32). SUB marks substitution cells.
    • Linked vars: VAR/DP0/DP1/GOT (heap pointers); quoted vars: BJV/BJ0/BJ1/BJM (de Bruijn levels).
    • DUP/MOV terms are [expr, body]; DUP/MOV nodes are shared expr slots.
9.6 HVM2 interaction summary (fast recall)
    • LINK: substitute the other occurrence of a VAR (non-local).
    • CALL: expand REF into a fresh dynamic net.
    • VOID: erase two nullary nodes.
    • ERASE: propagate eraser through binary nodes; copy NUM/REF.
    • COMMUTE: swap two different binary nodes.
    • ANNIHILATE: reduce two identical binary nodes into two redexes.
    • OPERATE: native numeric op on NUM nodes.
    • SWITCH: numeric switch (Nat-like) on NUM.
9.7 Self-test micro-cases (check yourself)
    • Label alignment: (&A{1,2}+&A{10,20}) → &A{11,22}; (&A{1,2}+&B{10,20}) → nested SUP (cross product).
    • APP-SUP: (&L{f,g} a) → !A &L= a; &L{(f A₀),(g A₁)}.
    • USE-SUP: (λ{f} &L{a,b}) → !F &L= f; &L{(λ{F₀} a),(λ{F₁} b)}.
    • EQL-LAM: (λax.af === λbx.bf) → X:=fresh; ax←X; bx←X; af===bf.
    • LINK deferral (HVM2): link x→A then x→B → first stores subst; second links A~B and clears x.
    • APP-RED-LAM: ((f ~> λx.g) a) → x←a; (f x)~>g (i.e., (f a)~>g[x:=a]).
    • APP-MAT-CTR: (λ{#K:h;m} #K{a,b}) → (h a b); (λ{#K:h;m} #L{a,b}) → (m #L{a,b}).
    • ALO-LAM: @{s} λx.f → fresh x'; λx'. @{x',s} f.
    • HVM2 REF dup safety: DUP meets REF @f with DUPs → unsafe; must expand/call or reject.
    • APP-CTR/NAM: (ctr a) or (name a) → ^(ctr a) / ^(name a).
    • CNF-LAM-ERA: cnf(λx.&{}) → &{} (ERA propagates).
    • CNF-LAM-SUP: cnf(λx.&L{a,b}) → &L{λx.a, λx.b} (binder quoted).
    • DP0/DP1 vs APP: no direct interaction; DUP pushes only via DUP-NOD/LAM/SUP/RED/DRY/NAM.
9.8 HVM2 memory/port cheat sheet (debugging)
    • Port: 32-bit = 3-bit tag + 29-bit value; nodes are just two ports (64-bit).
    • Port tag indicates the node it connects to; nodes themselves are typeless pairs.
    • NUM payload: 5-bit subtag + 24-bit data (U24/I24/F24 or operator tag).
    • Global state: node buffer + vars (substitution map) + redex bag.
    • Def.safe gates DUP-REF copy vs forced expansion.
    • 29-bit value bounds the node/var space; 64-bit versions lift this limit.
9.9 Common mis-rewrites (fast scan)
    • Treating DP0/DP1 or GOT as normal values; they must trigger DUP/MOV rules on the expr slot.
    • Introducing a DUP-APP interaction: DP0/DP1 never interacts with APP directly in HVM4.
    • Ignoring LAM_ERA_MASK: erasing lambdas skip substitution and affect DUP-LAM behavior.
    • Lifting all SUPs in CNF: only the first SUP is lifted per cnf step; others stay inside branches.
    • Treating RED as normal application: APP-RED has its own rule set and readback effects.

10) Reference & Continued Research
Not complete; keep searching and prefer primary sources. URLs are starting points, not exhaustive.
Primary interaction nets / combinators / implementations
    • Interaction nets implementation calculus + data structure model (Hassan/Mackie/Sato):
https://arxiv.org/pdf/1505.07164 (arXiv)
    • Sequential and concurrent abstract machines for interaction nets (Sousa Pinto, PDF):
https://link.springer.com/content/pdf/10.1007/3-540-46432-8_18.pdf (Springer)
    • Explicit framework for interaction nets (de Falco, LMCS PDF):
https://lmcs.episciences.org/1108/pdf (Logical Methods in Computer Science)
    • Fernández & Mackie “A Calculus for Interaction Nets” (landing pages; find accessible PDFs via institutional/author copies):
https://link.springer.com/chapter/10.1007/10704567_10 (Springer)
https://www.semanticscholar.org/paper/A-Calculus-for-Interaction-Nets-Fern%C3%A1ndez-Mackie/09eedea6d17793581afa3b3eb111bdadc98aadf3 (Semantic Scholar)
    • Lafont “Interaction Combinators” (Semantic Scholar entry; use it to locate the canonical PDF):
https://www.semanticscholar.org/paper/Interaction-Combinators-Lafont/6cfe09aa6e5da6ce98077b7a048cb1badd78cc76
λ-calculus sharing / optimal reduction background (classic starting points)
    • Asperti & Guerrini, The Optimal Implementation of Functional Programming Languages (book references; locate via publisher/author pages)
    • Barendregt, The Lambda Calculus: Its Syntax and Semantics (foundational reference)
HigherOrderCO / HVM4 / Bend (official docs & raw sources)
    • Local clone quick paths (use these first):
        ◦ hvm4/docs/theory/interaction_calculus.md
        ◦ hvm4/docs/hvm4/core.md
        ◦ hvm4/docs/hvm4/syntax.md
        ◦ hvm4/docs/hvm4/memory.md
        ◦ hvm4/docs/hvm4/collapser.md
        ◦ hvm4/docs/hvm4/interactions/
        ◦ HVM/paper/HVM2.pdf
        ◦ Bend/docs/dups-and-sups.md
        ◦ Bend/docs/using-scopeless-lambdas.md
        ◦ Bend/docs/compilation-and-readback.md
        ◦ Bend/docs/lazy-definitions.md
        ◦ Bend/docs/compiler-options.md
        ◦ Bend/docs/writing-fusing-functions.md
    • HVM4 repo README (build/run flags, examples):
https://raw.githubusercontent.com/HigherOrderCO/hvm4/main/README.md
    • HVM4 Interaction Calculus theory note:
https://raw.githubusercontent.com/HigherOrderCO/hvm4/main/docs/theory/interaction_calculus.md (GitHub)
    • HVM4 core grammar (core surface terms):
https://raw.githubusercontent.com/HigherOrderCO/hvm4/main/docs/hvm4/core.md
    • HVM4 parser syntax/desugaring rules:
https://raw.githubusercontent.com/HigherOrderCO/hvm4/main/docs/hvm4/syntax.md
    • HVM4 memory layout (64-bit terms, substitution cells, linked vs quoted):
https://raw.githubusercontent.com/HigherOrderCO/hvm4/main/docs/hvm4/memory.md
    • HVM4 collapser/CNF readback description:
https://raw.githubusercontent.com/HigherOrderCO/hvm4/main/docs/hvm4/collapser.md
    • HVM4 interaction rules directory (consult for exact rule coverage):
https://raw.githubusercontent.com/HigherOrderCO/hvm4/main/docs/hvm4/interactions/dup_sup.md
https://raw.githubusercontent.com/HigherOrderCO/hvm4/main/docs/hvm4/interactions/dup_lam.md
https://raw.githubusercontent.com/HigherOrderCO/hvm4/main/docs/hvm4/interactions/mov_sup.md (GitHub)
(and the rest of the docs/hvm4/interactions/ files)
    • HVM2 repo README (positioning, pointers to paper):
https://raw.githubusercontent.com/HigherOrderCO/HVM/main/README.md
    • HVM2 paper PDF:
https://raw.githubusercontent.com/HigherOrderCO/HVM/main/paper/HVM2.pdf
    • Bend docs on dups/sups and scopeless lambdas (useful applied intuition; also note stated restrictions):
https://raw.githubusercontent.com/HigherOrderCO/Bend/main/docs/dups-and-sups.md (GitHub)
https://raw.githubusercontent.com/HigherOrderCO/Bend/main/docs/using-scopeless-lambdas.md (GitHub)
https://raw.githubusercontent.com/HigherOrderCO/Bend/main/docs/compilation-and-readback.md (GitHub)
https://raw.githubusercontent.com/HigherOrderCO/Bend/main/docs/lazy-definitions.md (GitHub)
https://raw.githubusercontent.com/HigherOrderCO/Bend/main/docs/compiler-options.md (GitHub)
https://raw.githubusercontent.com/HigherOrderCO/Bend/main/docs/writing-fusing-functions.md (GitHub)
