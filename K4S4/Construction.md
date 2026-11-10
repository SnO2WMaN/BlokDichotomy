# The indexed S4 construction

**Status:** Lean-checked. This gives the concrete data used in
[Continuum many Kripke-complete S4 extensions of continuum degree](ContinuumManyDegreeContinuum.md).
The Lean proof uses the repository's existing definitions of general frames, normal logics, frame
equivalence, and degree.

## Frames and admissible sets

For $I\subseteq\mathbb N$, let $G_I$ have points
$$
r,h,o,o',\quad a_i,b_i,c_i,d_i,y_i\ (i\in\mathbb N),\quad e_i\ (i\in I).
$$
Write $x_{0,i}=a_i,x_{1,i}=b_i,x_{2,i}=c_i$, with column indices in
$\mathbb Z/3\mathbb Z$. Every nonterminal point sees both $o,o'$;
each terminal sees only itself. The other successors are specified as follows:

| Point | Nonterminal successors |
| --- | --- |
| $r$ | Every nonterminal point |
| $h$ | $h$ |
| $x_{k,m}$ | Itself; all ladder points at levels $n$ with $n+2\le m$; and $x_{k,m-1},x_{k+1,m-1}$ when $m>0$ |
| $d_m$ | Itself and all ladder points at levels at most $m$ |
| $e_m$ | Itself, $d_m$, all ladder points at levels at most $m$, and $a_{m+1}$ |
| $y_m$ | All ladder points, and $d_n,y_n$ for $m\le n$ |

These clauses define a reflexive, transitive, antisymmetric relation. They are
the full accessibility relation, including reflexive and transitively implied
edges. The ladder has cyclic adjacent pairs, the $d_i$ sit above whole levels, the
$e_i$ add one point from the next level, and the $y_i$ form an ascending chain.
Coding points are included only for indices in $I$; in Lean, their indices have
type `{n : ℕ // n ∈ I}`. Thus an absent coding point is absent from the frame's
underlying type.

Let $\mathcal F_I$ have underlying frame $G_I$. A set is admissible precisely
when membership along $y_0,y_1,\ldots$ is eventually constant. This is equivalent
to its trace on these points being finite or cofinite. Complements and finite
intersections preserve admissibility. For every set $X$, even an inadmissible
one, the trace of $\Diamond X$ is downward closed in $\mathbb N$: every
successor of $y_n$ is a successor of $y_m$ for $m\le n$. Such a trace is
either all of $\mathbb N$, or is contained in a finite initial segment.
Thus admissible sets are closed under $\Diamond$.

These facts are proved in [Basic.lean](Construction/Basic.lean) and
[Frame.lean](Construction/Frame.lean).

## Naming formulas

Use variables $p,q,s$. Let the Boolean types of $o,o',a,b,c,h$ be respectively
$$
111,\quad 000,\quad 100,\quad 010,\quad 001,\quad 110,
$$
where each digit prescribes the truth value of the corresponding variable.
Denote these formulas by $\lambda_o,\lambda_{o'},\lambda_k,\lambda_h$, for
$k\in\mathbb Z/3\mathbb Z$. Put
$$
\phi_o=\Box\lambda_o,\qquad \phi_{o'}=\Box\lambda_{o'},\qquad
\mu=\Diamond\phi_o\land\Diamond\phi_{o'}.
$$
Define
$$
\phi_{k,0}=\mu\land\lambda_k\land\Box(\mu\to\lambda_k),\qquad
\phi_h=\mu\land\lambda_h\land\Box(\mu\to\lambda_h).
$$
With $\tau_i=\bigvee_k\phi_{k,i}$, set
$$
\phi_{k,i+1}=\neg\tau_i\land\Diamond\phi_{k,i}
 \land\Diamond\phi_{k+1,i}\land\neg\Diamond\phi_{k+2,i}.
$$
The other names are
$$
\phi_{d_i}=\bigwedge_k\Diamond\phi_{k,i}\land\neg\Diamond\tau_{i+1},
$$
$$
\phi_{e_i}=\neg\phi_{d_i}\land\Diamond\phi_{d_i}\land
 \text{exactly one of the three }\Diamond\phi_{k,i+1},
$$
$$
\phi_{y_0}=\neg\phi_{d_0}\land\Diamond\phi_{d_0}
 \land\Diamond\phi_{d_1}\land\neg\Diamond\phi_h,
$$
$$
\phi_{y_{i+1}}=\neg\phi_{d_{i+1}}\land\Diamond\phi_{d_{i+1}}
 \land\Diamond\phi_{d_{i+2}}\land\neg\Diamond\phi_{d_i},
$$
$$
\phi_r=\bigwedge_k\Diamond\phi_{k,0}\land\Diamond\phi_h
 \land\Diamond\phi_{y_0}.
$$

For any valuation on $G_I$, if $\phi_r$ holds somewhere, these formulas
name $r,h,d_i,y_i$ exactly, and $\phi_{e_i}$ names $e_i$ if present and
is false everywhere otherwise. At each level the three ladder names are the
three singleton ladder points, possibly permuted. The permutation may depend
on the level: if $\phi_{k,i}$ names $x_{\pi_i(k),i}$, then
$$
\pi_{i+1}(k)=\pi_i(k+2)+1\pmod 3.
$$
The two terminal names can also be exchanged under an arbitrary valuation.
The argument identifies their pair and makes $\mu$ name precisely the
nonterminal points; it does not fix the individual terminal names.

Here is the naming argument, including the unrestricted-valuation step needed
for the main theorem. A root witness gives witnesses for all four base names.
Consequently both terminal names have witnesses. Any nonterminal witness for
one terminal name would force both terminals to have its Boolean type,
contradicting the existence of the other terminal name. Hence $\mu$ holds
exactly at nonterminal points.

Every nonterminal point sees a minimal nonterminal point. There are exactly
four such minima: $a_0,b_0,c_0,h$. Each base-name witness prescribes its
Boolean type at every minimal successor. The four types are incompatible, so
choosing one minimal successor for each witness gives an injection of four
elements into these four minima. It is a permutation. Every base-name witness
therefore sees only its assigned minimum. Inspection of the relation shows
that such a witness must itself be that minimum.

The marker name must name $h$. Otherwise one ladder base name names $h$.
The next-level formula asking for the other two ladder base names, while
excluding this one, has a witness at some level-one ladder point. Thus
$\tau_1$ has a witness. But a witness for $\phi_{d_0}$ would have to see
$h$ and other minima, forcing it to be $r$. This is impossible because
$r$ sees the witness for $\tau_1$. Since a root witness supplies a
$\phi_{d_0}$ witness through $\phi_{y_0}$, the contradiction pins the marker
to $h$.

Inductively, the three next-level points realize the three pairs from the
current level. The recursive formulas exclude the current level itself.
Other points see zero, one, or all three current-level points. This proves
the ladder naming statement. The remaining formulas now follow directly
from their successor patterns in the table.

The proofs are in [BasePoints.lean](Construction/BasePoints.lean),
[BaseNaming.lean](Construction/BaseNaming.lean),
[Marker.lean](Construction/Marker.lean), and
[Naming.lean](Construction/Naming.lean).

For the distinguished valuation, assign the indicated types to
$o,o',a_0,b_0,c_0,h$, and type $000$ elsewhere. It is admissible, since
all variables are false along the chain. The same induction proves that
$\phi_r$ holds at $r$, and every present coding point satisfies its name.
See [Distinguished.lean](Construction/Distinguished.lean).

## Excluding Kripke root witnesses

For fresh variables $u,v$, write $\eta_0=u$, $\eta_1=\neg u\land v$,
and $\Box^+A=A\land\Box A$. Let
$$
\sigma=\neg\bigl(\eta_0\land
 \Box^+(\eta_0\to\Diamond\eta_1)\land
 \Box^+(\eta_1\to\Diamond\eta_0)\bigr).
$$
An injective ascending chain in a transitive Kripke frame refutes $\sigma$:
put $\eta_0$ at even chain positions, $\eta_1$ at odd positions, and
neither elsewhere. This uses unrestricted Kripke valuations. In particular,
the chain $y_0Ry_1R\cdots$ shows that $G_I\not\models\sigma$; this
alternating valuation is not admissible on $\mathcal F_I$.

In contrast, $\mathcal F_I$ validates $\sigma$. A refutation would produce
a chain alternating between the two incompatible types. Antisymmetry makes
each step strict. Every point other than $r$ and the chain points has a finite
successor cone. An infinite strict chain therefore lies on the $y$-chain
after its first step, with strictly increasing indices. Admissibility of the
value of $u$ makes it eventually constant there, contradicting alternation.

Define
$$
\theta_i=\phi_r\to\Box\bigl(\phi_{y_i}\to
 \Diamond(\phi_{y_{i+1}}\land\neg\Diamond\phi_{y_i})\bigr),\qquad
\chi_i=\phi_r\to\neg\Diamond\phi_{e_i},
$$
and
$$
M=S4+\sigma+\{\theta_i:i\in\mathbb N\},\quad
L=\operatorname{Log}(\operatorname{Fr}(M)),\quad
L_I=M+\{\chi_i:i\notin I\}.
$$
The unrestricted naming argument proves $G_I\models\theta_i$ and
$G_I\models\chi_i$ whenever $i\notin I$. The distinguished valuation
refutes $\chi_i$ when $i\in I$. Therefore
$\mathcal F_I\models L_I$ and
$$
\chi_i\in L_I\ \Longleftrightarrow\ i\notin I,\qquad
G_I\models\chi_i\ \Longleftrightarrow\ i\notin I.
$$

Finally, any Kripke frame validating $M$ validates $\neg\phi_r$.
A root witness sees a $\phi_{y_0}$ witness. Successive applications of
$\theta_i$ produce an ascending chain whose next point cannot see the
previous one. This chain is injective by transitivity, contradicting
$\sigma$. Thus all $\chi_i$ belong to $L$, and adding any of them to
$M$ changes no validating Kripke frames:
$$
\operatorname{Fr}(L_I)=\operatorname{Fr}(M)=\operatorname{Fr}(L).
$$

These statements are proved in [Kripke.lean](Construction/Kripke.lean),
[Validity.lean](Construction/Validity.lean), and
[Logic.lean](Construction/Logic.lean). They supply every hypothesis of the
even/odd argument in the [main proof](ContinuumManyDegreeContinuum.md).
