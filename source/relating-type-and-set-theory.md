(idea from Navid)

**Logical Relations on Translations from Type Theory to Set Theory** (some ideas for LATIN)

Recall the theories`HardTyped = {tp: type, tm: tp -> type}`, `SoftTyped = {tp: type, term: type, of: term -> tp -> prop}`, and `SetTheory = {include FOL, ∈: set -> set -> prop}` (where `set` is an alias for `iota` from FOL).

We could have these translations:

1. a view `v1: HardTyped -> SoftTyped`: mapping`tp := term`, `tm := [x] term`
2. a view `v2: SoftTyped -> SetTheory`: mapping `tp := set`, `term := set`, `of := [x: set, T: set] x ∈ T`
3. a view `v3: HardTyped -> SetTheory = v1; v2` (defined as the composition of `v1`, `v2`), thus mapping `tp := set`, `tm := [x] set`

These represent the following meta theorems, respectively (obtained by the fact that views preserve typing judgements):

1. `|-_{HardTyped}  t: tm A  ==> |-_{SoftTyped}  v1(t): term`
2. `|-_{SoftTyped}  t: term, A: tp, pf: |~ of t A ==> |-_{SetTheory}  v2(s): set, v2(pf): |~ v2(t) ∈ v2(A)`
3. `|-_{HardTyped}  t: tm A ==> |-_{SetTheory}  v2(t): set`

Observe how the first and third meta theorems are rather unsatisfying: the type annotations `A` are lost!
In contrast, the second meta theorem looks nice: the assertion `|~ of t A` is preserved as `|~ v2(t) ∈ v2(A)`.

To overcome the unsatisfactory nature of the first and third views, we can *complement* them with the following logical relations:

- a logical relation `P: v1: HardTyped -> SoftTyped` partial on `tp`, mapping `tm := [T,x] |~ of x T`
- a logical relation `Q: v1 ; v2: HardTyped -> SetTheory := P ; v2`, i.e. the logical relation `P` post-composed by `v2`

These represent the meta theorems below (obtained by the respective Basic Lemmas):

- `|-_{HardTyped}  t: tm A  ==> |-_{SoftTyped}  P(t): |~ of v1(t) v1(A)`
- `|-_{HardTyped}  t: tm A ==> |-_{SetTheory}  v2(P(t)): |~ v2(v1(t)) ∈ v2(T)`

We can interpret these theorems, respectively, as **type preservation (from hard- to soft-typed)** and **"membership" preservation (when translating types to sets)**.