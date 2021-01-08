---
title: Formal Verification of Authenticated, Append-Only, Skip Lists in Agda
author: Victor Cacciari Miraldo, Harold Carr, Mark Moir, Lisandra Silva and Guy L. Steele Jr.
header-includes: |
  \usepackage{tikz}
  \usetikzlibrary{positioning}
  \usetikzlibrary{shapes}
  \usetikzlibrary{calc}
  \setbeamertemplate{itemize items}{>>}
  \setbeamertemplate{itemize subitem}{-}
monofont: DejaVuSansMono.ttf
---
\newcommand{\guydash}{-{\hskip-0.3em}-}
\newcommand{\hash}{\mathrm{hash}}
\newcommand{\rebuild}{\mathrm{rebuild}}
\newcommand{\hoptgt}{\hbox{\it hop\guydash{}tgt}}

# What, Why and How?

Formalized Authenticated Append-Only Skip Lists, originally from Maniatis and Baker ([arxiv pdf](http://arxiv.org/abs/cs/0302010))\footnote{`arxiv.org/abs/cs/0302010`}, in Agda:\pause

- Formalized a generalization of the original datastructure,\pause
- Formalized the security properties from Maniatis and Baker,\pause
- Proved the proposed generalization satisfies the security properties,\pause
- Proved Maniatis and Baker's AAOSL is an instance of our generalization.\pause

Uncovered interesting simplifications and made the security argument clearer\pause

# Traditional Append-Only Structures: Blockchains

- Only _lookup_ and _append_ operations\pause
- Entry $n+1$ depends on hash of entry $n$
\vfill
\begin{tikzpicture}
	\node (gen) {$\star$};
	\pause
	\node [right = of gen] (e1) {$e_1$};
	\draw[->] (e1.north west) to[out=135, in=45] (gen.north east);
	\pause
	\node [right = of e1] (e2) {$e_2$};
	\draw[->] (e2.north west) to[out=135, in=45] (e1.north east);
	\pause
	\node [right = of e2] (elipsis) {$\cdots$};
	\draw[->] (elipsis.north west) to[out=135, in=45] (e2.north east);
	\node [right = of elipsis] (en) {$e_n$};
	\draw[->] (en.north west) to[out=135, in=45] (elipsis.north east);
	\node [right = of en] (en1) {$e_{n+1}$};
	\draw[->] (en1.north west) to[out=135, in=45] (en.north east);
\onslide<1->
\end{tikzpicture}
\vfill
\pause
- Prevent attacker rewriting history:
  + agree on $\hash\;e_{n+1}$ implies agree on $\hash\;e_n$\pause

- Works well with static membership and no garbage collection

\vfill

# Traditional Append-Only Structures: Blockchains

Or, in Haskell:

```haskell
data Auth a = Auth a Digest

digest :: Auth a -> Digest
digest (Auth _ dig) = dig

type Log a = [Auth a]

append :: (Hashable a) => a -> Log a -> Log a
append x l = mkauth x l : l
```
\pause
```haskell
mkauth :: (Hashable a) => a -> Log a -> Auth a
mkauth x []              = error "Log not initialized"
mkauth x (Auth y dy : l) = Auth x (hash (hash x ++ dy))
```


# Problem: Dynamic Participation

\vfill
\begin{tikzpicture}
	\node (gen) {$\star$};
	\node [right = of gen] (e1) {$e_1$};
	\draw[->] (e1.north west) to[out=135, in=45] (gen.north east);
	\node [right = of e1] (e2) {$e_2$};
	\draw[->] (e2.north west) to[out=135, in=45] (e1.north east);
	\node [right = of e2] (elipsis) {$\cdots$};
	\draw[->] (elipsis.north west) to[out=135, in=45] (e2.north east);
	\node [right = of elipsis] (en) {$e_n$};
	\draw[->] (en.north west) to[out=135, in=45] (elipsis.north east);
	\node [right = of en] (en1) {$e_{n+1}$};
	\draw[->] (en1.north west) to[out=135, in=45] (en.north east);
	\pause
	\node [below = of en1] (p) {Participant $p$ joins};
	\draw[->] (p) -- (en1);
\onslide<1->
\end{tikzpicture}
\vfill
\pause

- New participant needs either:
  1. Download the entire history and compute state $s_{n+1}$\pause
  1. Download a "checkpoint" package
	 + copy of $s_{n+1}$
	 + enough signatures over $\hash\;e_{n+1}$\pause

- Option (2) is better: log always increases
\vfill

# Dynamic Participation: Verifying Claims

Say $p$ began participation at $n$, \pause now say $p$ receives a claim about some
entry $e_i$, for $i < n$. How should $p$ check the claim's veracity?

\pause
\vfill

1. Download entries between $i$ and $n$; rebuild the hashes; check
rebuild hash for $e_n$ against known one\pause
1. Forward the claim to some other participant\pause

\vfill

After a few rounds of dynamic participation no participant might contain all entries.

\vfill

# Authenticated Append-Only Skip Lists (AAOSL)

- Originally from Maniatis and Maniatis ([arxiv pdf](http://arxiv.org/abs/cs/0302010))
- Make $\hash\;e_n$ depend on more than one entry.\pause
  + Let $n = 2^l \times d$, for an odd $d$, $\hash\;e_d$ will depend
  on $e_i$, $i \in \{ e_{2^l \times d - 2^k} \mid k \leq l \}$.\pause

\resizebox{\textwidth}{!}{\begin{tikzpicture}
	\node (gen) {$\star$};
	\node [right = of gen] (e1) {$e_1$};
	\draw[->] (e1.north west) to[out=135, in=45] (gen.north east);
	\node [right = of e1] (e2) {$e_2$};
	\draw[->] (e2.north west) to[out=135, in=45] (e1.north east);
	\node [right = of e2] (e3) {$e_3$};
	\draw[->] (e3.north west) to[out=135, in=45] (e2.north east);
	\node [right = of e3] (e4) {$e_4$};
	\draw[->] (e4.north west) to[out=135, in=45] (e3.north east);
	\node [right = of e4] (e5) {$e_5$};
	\draw[->] (e5.north west) to[out=135, in=45] (e4.north east);
	\node [right = of e5] (e6) {$e_6$};
	\draw[->] (e6.north west) to[out=135, in=45] (e5.north east);
	\node [right = of e6] (e7) {$e_7$};
	\draw[->] (e7.north west) to[out=135, in=45] (e6.north east);
	\node [right = of e7] (e8) {$e_8$};
	\draw[->] (e8.north west) to[out=135, in=45] (e7.north east);
	\node [right = of e8] (e9) {$e_9$};
	\draw[->] (e9.north west) to[out=135, in=45] (e8.north east);
	\pause
	\draw[->] ($ (e2.north west) + (.1,0) $) to[out=110,in=70] ($ (gen.north east) - (.1,0) $);
	\draw[->] ($ (e4.north west) + (.1,0) $) to[out=110,in=70] ($ (e2.north east) - (.1,0) $);
	\draw[->] ($ (e6.north west) + (.1,0) $) to[out=110,in=70] ($ (e4.north east) - (.1,0) $);
	\draw[->] ($ (e8.north west) + (.1,0) $) to[out=110,in=70] ($ (e6.north east) - (.1,0) $);
	\pause
	\draw[->] ($ (e4.north west) + (.2,0) $) to[out=105,in=75] ($ (gen.north east) - (.2,0) $);
	\draw[->] ($ (e8.north west) + (.2,0) $) to[out=105,in=75] ($ (e4.north east) - (.2,0) $);
	\pause
	\draw[->] ($ (e8.north west) + (.3,0) $) to[out=100,in=90] ($ (gen.north east) - (.3,0) $);
\onslide<1->
\end{tikzpicture}}

\pause
- The _level_ of $n = 2^l*d$ is defined as $l+1$
  + Indicates number of dependencies of $n$.
  + Example: level of $8 = 2^3 \times 1$ is $4$.

# Append-Only Authenticated Skip Lists (AAOSL)

Or, in Haskell:

```haskell
append :: (Hashable a) => a -> Log a -> Log a
append x l = mkauth x l : l
```
\pause
```haskell
mkauth :: (Hashable a) => a -> Log a -> Auth a
mkauth a log =
  let  j     = length log
       deps  = [ digest (log ! j - pow 2 l)
               | l <- [0 .. level j - 1] ]
  in Auth a (auth j (hash a) deps)
```
\pause
```haskell
auth :: Index -> Digest -> [Digest] -> Digest
auth j datumDig lvlDigs =
  hash (concat (encode j : datumDig : lvlDigs))
```

# Advancement Proofs

- Proves to a verifier that log advanced from $i$
to $j \geq i$\pause

- Example: an advancement proof from 7 to 12
  + enables to construct $\hash\;e_{12}$ given $\hash\;e_{7}$ \pause

\resizebox{\textwidth}{!}{\begin{tikzpicture}
	\node (e6) {$e_6$};
	\node (e5) at ($ (e6) - (.9,-.4) $) {$e_5$};
	\node (e4) at ($ (e5) + (0,.8) $) {$e_4$};
	\node (gen) at ($ (e4) + (0,.7) $) {$\star$};
	\draw[->] (e6.north west) to[out=135, in=0] (e5.east);
	\node [right = of e6] (e7) {$e_7$};
	\draw[->] (e7.north west) to[out=135, in=45] (e6.north east);
	\node [right = of e7] (e8) {$e_8$};
	\draw[->, very thick, color=blue!70!black] (e8.north west) to[out=135, in=45] (e7.north east);
	\node [right = of e8] (e9) {$e_9$};
	\draw[->] (e9.north west) to[out=135, in=45] (e8.north east);
	\node [right = of e9] (e10) {$e_{10}$};
	\draw[->] (e10.north west) to[out=135, in=45] (e9.north east);
	\node [right = of e10] (e11) {$e_{11}$};
	\draw[->] (e11.north west) to[out=135, in=45] (e10.north east);
	\node [right = of e11] (e12) {$e_{12}$};
	\draw[->] (e12.north west) to[out=135, in=45] (e11.north east);
	\draw[->] ($ (e6.north west) + (.1,0) $) to[out=110,in=345] (e4.south east);
	\draw[->] ($ (e8.north west) + (.1,0) $) to[out=110,in=70] ($ (e6.north east) - (.1,0) $);
	\draw[->] ($ (e10.north west) + (.1,0) $) to[out=110,in=70] ($ (e8.north east) - (.1,0) $);
	\draw[->] ($ (e12.north west) + (.1,0) $) to[out=110,in=70] ($ (e10.north east) - (.1,0) $);
	\draw[->] ($ (e8.north west) + (.2,0) $) to[out=105,in=0] (e4.east);
	\draw[->] ($ (e8.north west) + (.3,0) $) to[out=100,in=0] ($ (gen.east) + (0.05,0) $);
	\draw[->, very thick, color=blue!70!black] ($ (e12.north west) + (.2,0) $) to[out=105,in=75] ($ (e8.north east) - (.2,0) $);
	\pause
	\node [circle, draw=blue!70!black, inner sep=2.2mm] (c11) at (e11) {};
	\node [circle, draw=blue!70!black, inner sep=2.2mm] (c10) at (e10) {};
	\node [circle, draw=blue!70!black, inner sep=2.2mm] (c6) at (e6) {};
	\node [circle, draw=blue!70!black, inner sep=2.2mm] (c4) at (e4) {};
	\node [circle, draw=blue!70!black, inner sep=2.2mm] (cgen) at (gen) {};
\onslide<1->
\end{tikzpicture}}

\pause
```haskell
adv7_12 ~ ( Hop d12 12 2 (Hop d8 8 0 Done)
          , M.fromList [ (i, digestFor log i)
                       | i <- [0,4,6,10,11] ])
```

# Advancement Proofs

```haskell
rebuild :: AdvProof -> Digest -> Digest
```
\pause
\vfill

```haskell
adv7_12 ~ ( Hop d12 12 2 (Hop d8 8 0 Done)
          , M.fromList [ (i, digestFor log i)
                       | i <- [0,4,6,10,11] ])
```
\pause
\vfill
```haskell
rebuild adv7_12 my_h7
  = let r8  = auth 8  d8  [my_h7, h6, h4, h0]
        r12 = auth 12 d12 [h11,h10,r8]
    in r12
```
\vfill

# Membership Proofs

Prove datum $d$ is in index $i$ for someone who trusts
the digest $\hash\;e_j$ for $j \geq i$.\pause
\vfill

Consists of an advancement proof from $i$ to $j$,
the dependencies of $i$ and the data at $i$.
\vfill

Say we want to prove data at position 7 is $d7$:
```haskell
mem7_12 ~ ( d7 , adv7_12 `add_auth_to_map` [(6, h6)])
```
\vfill

# Membership Proofs: Rebuilding a Root
Say we want to prove data at position 7 is $d7$:
```haskell
mem7_12 ~ ( d7 , adv7_12 `add_auth_to_map` [(6, h6)])
```
\pause\vfill

Since `h6` was already present, `adv7_12` does not change:
```haskell
mem7_12 ~ ( d7 , ( Hop d12 12 2 (Hop d8 8 0 Done)
                 , M.fromList [ (i, digestFor log i)
                              | i <- [0,4,6,10,11] ]))
```
\pause\vfill

Rebuilding now takes an extra step:
```haskell
rebuild_mem mem7_12
  = let r7  = auth 7  d7 [h6]
        r8  = auth 8  d8 [r7, h6, h4, h0]
        r12 = auth 12 d12 [h11,h10,r8]
    in r12
```

#

\begin{center}
\Huge
\color{blue!65!black}{Security Properties}
\end{center}

# Agree On Common

\pause

\begin{center}
\resizebox{0.9\textwidth}{!}{\begin{tikzpicture}[
  verA/.style = {color=blue!70!black},
  verB/.style = {color=yellow!60!black}]
	\node (j) {$j$};
	\node (i1)  at ($ (j) - (8,-1) $) {$i_1$};
	\node (i2)  at ($ (j) - (9, 1) $) {$i_2$};
	\onslide<2>{ \draw[->, verA] (j.north west) to[out=105, in=25] node[midway, above]{$a_1$} (i1);
                 \draw[->, verB] (j.south west) to[out=255, in=-25] node[midway, below]{$a_2$} (i2); }
	\pause
	\onslide<3->{ \draw[->, verA] (j.north west) to[out=105, in=25] node[midway, above]{$a_1 = a_{11} \oplus \cdots \oplus a_{14} $} (i1);
                  \draw[->, verB] (j.south west) to[out=255, in=-25] node[midway, below]{$a_2 = a_{21} \oplus \cdots \oplus a_{24} $} (i2); }
	\node (s11) at ($ (i1) + (6,0) $)  {$s_1$};
	\node (s12) at ($ (s11) - (0,2) $) {$s_1$};
	\node (x) at ($ (i1) + (4.5,0) $) {$x$};
	\node (s21) at ($ (i1) + (3,0) $) { $s_2$ };
	\node (s22) at ($ (s21) - (0, 2) $) { $s_2$ };
	\node (y) at ($ (i2) + (3,0) $) {$y$};
	\draw[->, verA] (j.north west) to[out=135, in=0] node[near end, above]{$a_{14}$} (s11);
	\draw[->, verA] (s11) -- node[midway, above]{$a_{13}$} (x)
	                      -- node[midway, above]{$a_{12}$} (s21)
						  -- node[midway, above]{$a_{11}$} (i1);
	\draw[->, verB] (j.south west) to[out=225, in=0] node[near end, below]{$a_{24}$} (s12);
	\draw[->, verB] (s12) -- node[midway, below]{$a_{23}$} (s22)
		                  -- node[midway, below]{$a_{22}$} (y)
						  -- node[midway, below]{$a_{21}$} (i2);
	\pause
	\node (eq1) at ($ (s11)!0.5!(s12) $) {$\equiv$};
	\node (eq2) at ($ (s21)!0.5!(s22) $) {$\equiv$};
\onslide<1->
\end{tikzpicture}}
\end{center}

\onslide<1->{If $\rebuild\;a_1\;j \equiv \rebuild\;a_2\;j$}
\onslide<4->{, then $\rebuild\;a_1\;s_1 \equiv \;rebuild\;a_2\;s_1$ and $\rebuild\;a_1\;s_2 \equiv \rebuild\;a_2\;s_2$ }

# Evolutionary Collision Resistance

\pause

\begin{center}
\resizebox{0.9\textwidth}{!}{\begin{tikzpicture}[
  verA/.style = {color=blue!70!black},
  verB/.style = {color=yellow!60!black}]
	\node (j) {$j$};
	\node (i1)  at ($ (j) - (8,-1) $) {$i_1$};
	\node (i2)  at ($ (j) - (9, 1) $) {$i_2$};
	\onslide<2> { \draw[->, verA] (j.north west) to[out=105, in=25] node[midway, above]{$a_1$} (i1);
                  \draw[->, verB] (j.south west) to[out=255, in=-25] node[midway, below]{$a_2$} (i2); }
	\pause
	\onslide<3-> { \draw[->, verA] (j.north west) to[out=105, in=25] node[midway, above]{$a_1 = a_{11} \oplus a_{12} $} (i1);
                   \draw[->, verB] (j.south west) to[out=255, in=-25] node[midway, below]{$a_2 = a_{21} \oplus a_{22} $} (i2); }
	\node (s1) at ($ (i1) + (5,0) $) {$s_1$};
	\node (s2) at ($ (i2) + (5,0) $) {$s_2$};
	\draw[->, verA] (j.north west) to[out=135, in=0] node[midway, above]{$a_{12}$} (s1);
	\draw[->, verA] (s1) -- node[midway, above]{$a_{11}$} (i1);
	\draw[->, verB] (j.south west) to[out=225, in=0] node[midway, below]{$a_{22}$} (s2);
	\draw[->, verB] (s2) -- node[midway, below]{$a_{21}$} (i2);
	\pause
	\node (tgt) at ($ (j) - (6.2, 0) $) {$tgt$};
	\draw[->, dashed, thick, verA] (tgt.north east) to[out=45, in=195] node[midway, below]{$m_1$} (s1);
	\draw[->, dashed, thick, verB] (tgt.south east) to[out=-45, in=165] node[midway, above]{$m_2$} (s2);
\onslide<1->
\end{tikzpicture}}
\end{center}

\onslide<2->{If $\rebuild\;a_1\;j \equiv \rebuild\;a_2\;j$}
\onslide<4->{and $\rebuild\;m_i\;s_i \equiv \rebuild\;a_i\;s_i$, then}
\onslide<5->{$m_1$ and $m_2$ authenticate the same data.}


# Semi-Evolutionary Collision Resistance

Interpretation mistake: our paper proved something \emph{less} general:

\pause

\begin{center}
\resizebox{0.8\textwidth}{!}{\begin{tikzpicture}[
  verA/.style = {color=blue!70!black},
  verB/.style = {color=yellow!60!black}]
	\node (j) {$j$};
	\node (i1)  at ($ (j) - (8,-1) $) {$i_1$};
	\node (i2)  at ($ (j) - (9, 1) $) {$i_2$};
	\draw[->, verA] (j.north west) to[out=105, in=25] node[midway, above]{$a_1 = a_{11} \oplus a_{12} \oplus a_{13} $} (i1);
	\draw[->, verB] (j.south west) to[out=255, in=-25] node[midway, below]{$a_2 = a_{21} \oplus a_{22} \oplus a_{23} $} (i2);
	\node (s1) at ($ (i1) + (5,0) $) {$s_1$};
	\node (s2) at ($ (i2) + (5,0) $) {$s_2$};
	\node (tgt1) at ($ (j) - (6.2, -1) $) {$tgt$};
	\node (tgt2) at ($ (j) - (6.2, 1) $) {$tgt$};
	\draw[->, verA] (j.north west) to[out=135, in=0] node[midway, above]{$a_{13}$} (s1);
	\draw[->, verA] (s1) -- node[midway, above]{$a_{11}$} (tgt1) -- node[near start, above]{$a_{12}$} (i1);
	\draw[->, verB] (j.south west) to[out=225, in=0] node[midway, below]{$a_{23}$} (s2);
	\draw[->, verB] (s2) -- node[midway, below]{$a_{21}$} (tgt2) -- node[midway, below]{$a_{22}$} (i2);
	\draw[->, dashed, thick, verA] (tgt1.south east) to[out=-45, in=200] node[near end, below]{$m_1$} (s1);
	\draw[->, dashed, thick, verB] (tgt2.north east) to[out=45, in=160] node[near end, above]{$m_2$} (s2);
\onslide<1->
\end{tikzpicture}}
\end{center}

\pause

Already fixed! Same \textsc{evo-cr} as original authors available
at [`github.com/oracle/aaosl-agda`](https://github.com/oracle/aaosl-agda)

# Which AAOSL's enjoy \textsc{aoc} and \textsc{evo-cr}?

Nothing special about building the skiplist with powers of 2\pause

In fact, any skiplist such that hops never \emph{cross} will enjoy \textsc{AOC} and \textsc{EVO-CR}

\vfill

\begin{center}
\resizebox{.7\textwidth}{!}{
\begin{tikzpicture}
  \node                      (h1) {$h_1$};
  \node [above = of h1]      (h2) {$h_2$};
  \node [below left = of h1] (tgt1) {$\hoptgt\;h_1$};
  \node [left = of tgt1]     (tgt2) {$\hoptgt\;h_2$};
  \node [below right = of h1] (j1p) {};
  \node [right = of j1p]       (j2) {$j_2$};
  \node (form)  at ($ (tgt2)!0.5!(tgt1) $) {$<$};
  \node (form3) at ($ (tgt1)!0.5!(j1p) $) {$<$};
  \draw [line width=0.25mm, ->] (j2) |- (h2.south) -| (tgt2);
  \draw [line width=0.25mm, ->] (h1.south) -| (tgt1);
  \pause
  \node (j1) at (j1p) {$j_1$};
  \node (form2) at ($ (j1)!0.5!(j2)     $) {$\leq$};
  \draw [line width=0.25mm] (j1) |- (h1.south);
\onslide<1->
\end{tikzpicture}}
\end{center}

\vfill

\pause

If $\hoptgt\;h_2 < \hoptgt\;h_1$ and $hoptgt\;h_1 < j_2$, then $j_1 \leq j_2$.

\vfill

# Working Modulo Hash Collisions

The security proofs happen modulo hash collisions. \pause

AAOSL enjoys \textsc{EVO-CR} iff an adversary cannot
invert the hash function in polynomial time.\pause

Our Agda development was made modulo _existential_ hash collisions:
```agda
HashBroke : Set
HashBroke = ∃[ (x , y) ] (x ≢ y × hash x ≡ hash y)

prop : A → B → ⋯ → Either HashBroke Result
```

\pause

Unfortunate: requires manual inspection
that collisions are constructed from data
provided in `A`, `B`, etc., in polynomial time.

\pause

No different than checking a pen-and-paper proof, though.

# Future Work: Explicit Hash Collisions

Instead of:

```agda
prop : A → B → ⋯ → Either HashBroke Result
```

\vfill
\pause

Define a relaton `prop-HB` capturing where the collisions can come from in `prop`:

```agda
prop : (a : A) → (b : B) → ⋯ → Either (prop-HB a b ⋯) Result

collision : prop-HB a b ⋯ → HashBroke
```
Only have to check `collision` runs in polynomial time.

\vfill
\pause

Non-trivial effort: every Agda function `f` needs its own `f-HB` relation

\vfill

# Conclusions

Machine checked the claims from Maniatis and Baker: AAOSL does enjoy \textsc{evo-cr}.

\vfill
\pause

Formal model in Agda enabled experimentation.\pause

- Simpler advancement proof definition
- Simpler `auth` function definition
    + Core principle: `auth j d hs ≡ auth j d' hs'` implies `d ≡ d'` and `hs ≡ hs'` modulo hash collisions

\vfill
\pause

Being precise is important, even on paper. Maniatis and Baker's original description of \textsc{evo-cr}
is in plain english, which means we had to interpret it, and we missed a detail.
