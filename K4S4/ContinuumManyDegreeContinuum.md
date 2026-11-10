# Continuum many Kripke-complete S4 extensions of continuum degree

**Status:** Lean-checked. The concrete construction is described in
[The indexed S4 construction](Construction.md) and formalized under
[`Construction/`](Construction/). The main results in
[`ContinuumManyDegreeContinuum.lean`](ContinuumManyDegreeContinuum.lean) are
`Modal.K4S4.exists_complete_continuum_degree_family` and
`Modal.K4S4.mk_complete_continuum_degree_eq_continuum`. The first also gives
pairwise distinct classes of validating frames; the second states the exact
cardinality of all Kripke-complete S4 extensions of continuum S4 degree.

The reusable intersection lemmas are in
[`Degree.lean`](Kripke/Degree.lean), including
`NormalLogic.FrameEquiv.inter` and `NormalLogic.KripkeComplete.inter`.
The formalization uses formulas over natural-number variables and all frames
in `Type`, as below. Check it with `lake build K4S4 --wfail`.

**Theorem.** There are $2^{\aleph_0}$ pairwise distinct Kripke-complete normal
extensions of $\mathsf{S4}$, each of degree $2^{\aleph_0}$ in
$\operatorname{NExt}\mathsf{S4}$. Their classes of validating Kripke frames are
pairwise distinct.

All formulas use a fixed countably infinite set of propositional variables.
Throughout, degree counts companions extending $\mathsf{S4}$, with equivalence
tested on all Kripke frames:

$$
\deg_{\operatorname{NExt}\mathsf{S4}}(A)
=\left|\{H\in\operatorname{NExt}\mathsf{S4}:
  \operatorname{Fr}(H)=\operatorname{Fr}(A)\}\right|.
$$

The idea is to split the indexed construction's indices into two infinite sets.
One set distinguishes the Kripke-complete logics; the other distinguishes
continuum many companions of each one.

## 1. The information supplied by the indexed construction

For the construction in [Construction.md](Construction.md), write

$$
M=\mathsf{S4}+\sigma+\{\theta_n:n\in\omega\},\qquad
L=\operatorname{Log}(\operatorname{Fr}(M)),
$$

$$
L_I=M+\{\chi_n:n\in\omega\setminus I\}
\quad(I\subseteq\omega),\qquad
\chi_n=\phi_r\to\neg\Diamond\phi_{e_n}.
$$

The construction establishes

$$
\operatorname{Fr}(L_I)=\operatorname{Fr}(L),\qquad
L_I\subseteq L,\qquad
\chi_n\in L\quad(n\in\omega).
\tag{1}
$$

Moreover, its general frame $\mathcal F_I$ validates $L_I$, and its distinguished
valuation $V^*$ refutes $\chi_n$ whenever $n\in I$. Together with the definition
of $L_I$, this gives the exact membership pattern

$$
\chi_n\in L_I\quad\Longleftrightarrow\quad n\notin I.
\tag{2}
$$

We need one further observation about the same frames. Write $G_J$ for the
**underlying Kripke frame** of $\mathcal F_J$, allowing all valuations, and put

$$
C_J=\operatorname{Log}(G_J).
$$

**Lemma.** For every $J\subseteq\omega$ and $n\in\omega$,

$$
\chi_n\in C_J\quad\Longleftrightarrow\quad n\notin J.
\tag{3}
$$

*Proof.* The naming lemma in [Construction.md](Construction.md) holds for
arbitrary valuations on $G_J$.
Its proof uses only the relation and the Boolean types: it first identifies the
two terminal points, then the four minimal nonterminal points, and then the
ladder levels and the remaining named points. No step uses the finite-or-cofinite
restriction on valuations along $Y$. That restriction is used separately to
prove validity of $\sigma$ in the general frame.

If $n\notin J$, consider any valuation on $G_J$. If $\phi_r$ is false everywhere,
$\chi_n$ is true everywhere. Otherwise the unrestricted naming lemma applies:
$\phi_r$ names $r$, and $\phi_{e_n}$ is false everywhere because $e_n$ is absent.
Again $\chi_n$ is true everywhere. Thus $G_J\models\chi_n$.

If $n\in J$, the distinguished valuation $V^*$ is also a valuation on $G_J$.
At $r$ it satisfies $\phi_r\land\Diamond\phi_{e_n}$, so it refutes $\chi_n$.
This proves (3). $\square$

In particular, the passage to all valuations preserves the coding by the
$\chi_n$, even though validity of $\sigma$ is lost.

## 2. Frame equivalence is preserved under intersection

We use the following elementary fact about normal extensions of $\mathsf{S4}$.

**Lemma.** If $A,A',B\in\operatorname{NExt}\mathsf{S4}$ and
$\operatorname{Fr}(A)=\operatorname{Fr}(A')$, then

$$
\operatorname{Fr}(A\cap B)=\operatorname{Fr}(A'\cap B).
\tag{4}
$$

*Proof.* First let $F$ be a rooted reflexive transitive frame. Then

$$
F\models A\cap B
\quad\Longleftrightarrow\quad
F\models A\ \text{or}\ F\models B.
\tag{5}
$$

The right-to-left implication is immediate. For the converse, suppose $F$
refutes $A$ and $B$. Choose $\varphi\in A$ refuted at some point and
$\psi\in B$ refuted at some point. By injectively renaming their variables into
two disjoint infinite sets, we may combine the two refuting valuations into a
single valuation. Write $\varphi',\psi'$ for the renamed formulas.
The root sees both refutation points, so this valuation refutes

$$
\Box\varphi'\lor\Box\psi'
$$

at the root. But this formula belongs to both $A$ and $B$, by substitution,
necessitation, and propositional reasoning. This contradicts
$F\models A\cap B$ and proves (5).

For an arbitrary reflexive transitive frame $F$, let $F_x$ be the rooted
generated subframe on the successors of $x$. Validity on $F$ is equivalent to
validity on every $F_x$: truth at $x$ depends only on this generated subframe.
Applying (5) gives

$$
F\models A\cap B
\quad\Longleftrightarrow\quad
\text{for every }x,\quad F_x\models A\ \text{or}\ F_x\models B.
$$

Replacing $A$ by $A'$ preserves this condition. Finally, any frame validating
either intersection validates $\mathsf{S4}$ and is therefore reflexive and
transitive. Frames outside that class validate neither intersection. This
proves (4) on all Kripke frames. $\square$

## 3. Two independent parameters

Partition the indices into the even and odd numbers:

$$
E=\{2n:n\in\omega\},\qquad O=\{2n+1:n\in\omega\}.
$$

For $J\subseteq O$, define

$$
Q_J=L\cap C_J.
$$

For $I\subseteq E$ and $J\subseteq O$, define

$$
P_{I,J}=L_I\cap C_J.
$$

Every one of these logics is a normal extension of $\mathsf{S4}$: the indexed
logics extend $\mathsf{S4}$, and each $G_J$ is reflexive and transitive.

**Each $Q_J$ is Kripke complete.** Indeed,

$$
Q_J
=\operatorname{Log}\bigl(\operatorname{Fr}(M)\cup\{G_J\}\bigr),
\tag{6}
$$

because the logic of a union of frame classes is the intersection of their
logics.

**The $Q_J$ are pairwise distinct, with different validating frames.** By (1)
and (3),

$$
\chi_n\in Q_J\quad\Longleftrightarrow\quad n\notin J.
\tag{7}
$$

If $J\neq J'$, exchange them if necessary and choose $n\in J\setminus J'$.
Then $\chi_n\in Q_{J'}$ but $\chi_n\notin Q_J$.
More concretely, $G_J$ validates $Q_J\subseteq C_J$, but refutes
$\chi_n\in Q_{J'}$. Thus

$$
\operatorname{Fr}(Q_J)\neq\operatorname{Fr}(Q_{J'}).
\tag{8}
$$

**For each fixed $J$, all the $P_{I,J}$ have the same validating frames as
$Q_J$.** Apply (4) to (1), intersecting with $C_J$:

$$
\operatorname{Fr}(P_{I,J})
=\operatorname{Fr}(L_I\cap C_J)
=\operatorname{Fr}(L\cap C_J)
=\operatorname{Fr}(Q_J).
\tag{9}
$$

**For each fixed $J$, the $P_{I,J}$ are pairwise distinct as $I$ varies.**
Every even-indexed $\chi_n$ belongs to $C_J$, by (3), since $J\subseteq O$.
Hence (2) gives

$$
\chi_n\in P_{I,J}\quad\Longleftrightarrow\quad n\notin I
\qquad(n\in E).
\tag{10}
$$

Thus different subsets of $E$ give different companions of $Q_J$.

There are $2^{\aleph_0}$ choices of $I\subseteq E$. By (9) and (10),

$$
2^{\aleph_0}
\leq\deg_{\operatorname{NExt}\mathsf{S4}}(Q_J)
\leq 2^{\aleph_0}.
$$

The last inequality holds because a normal modal logic is a subset of the
countable set of modal formulas. Consequently every $Q_J$ has degree exactly
$2^{\aleph_0}$ in $\operatorname{NExt}\mathsf{S4}$.

Finally, there are $2^{\aleph_0}$ choices of $J\subseteq O$. Equations (6) and
(8) give the required continuum many Kripke-complete logics, belonging to
continuum many different Kripke-equivalence classes. $\square$
