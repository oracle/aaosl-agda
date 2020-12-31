---
title: Formal Verification of Authenticated, Append-Only, Skip Lists in Agda
author: Victor Cacciari Miraldo, Harold Carr, Mark Moir, Lisandra Silva and Guy L. Steele Jr.
header-includes: |
  \usepackage{tikz}
  \usetikzlibrary{positioning}
  \usetikzlibrary{shapes}
  \usetikzlibrary{calc}
---

\newcommand{\hash}{\mathrm{hash}}

# Traditional Append-Only Structures: Blockchains

- Only _lookup_ and _append_ operations\pause
- Block $n+1$ depends on block $n$
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
  + We agree on $\hash\;e_{n+1}$ implies we agree on $\hash\;e_n$\pause

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

# Append-Only Authenticated Skip Lists (AAOSL)

- Originally from Baker and Maniatis ([arxiv pdf](http://arxiv.org/abs/cs/0302010))
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

- Example: an $AdvProof$ from 7 to 12
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
adv7_12 = ( Hop d12 12 2 (Hop d8 8 0 Done)
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
adv7_12 = ( Hop d12 12 2 (Hop d8 8 0 Done)
          , M.fromList [ (i, digestFor log i)
                       | i <- [0,4,6,10,11] ])
```
\pause
\vfill
```haskell
rebuild adv7_12 my_h7
  = let r8  = auth 8  d8 [my_h7, h6, h4, h0]
        r12 = auth 12 d12 [h11,h10,r8]
    in r12
```
\vfill

# Membership Proofs

# The Core Security Principle(s)

# The Knapking Security Proof

# AAOSL In Agda

# Future Work and Conclusions
