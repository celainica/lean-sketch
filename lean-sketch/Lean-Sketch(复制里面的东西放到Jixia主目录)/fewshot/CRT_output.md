**Theorem:** Let $a, b, m, n$ be natural numbers. If $m$ and $n$ are coprime, then the following equivalence holds:
$$ a \equiv b \pmod m \land a \equiv b \pmod n \iff a \equiv b \pmod{m \cdot n} $$

---

**Proof of Theorem:**

We prove both directions of the equivalence.

($\Rightarrow$) Assume that $a \equiv b \pmod m$ and $a \equiv b \pmod n$. The definition of modular congruence states that $a \equiv b \pmod k$ if and only if $k$ divides the difference $a-b$. Therefore, our assumptions are equivalent to:
$$ m \mid (a-b) \quad \text{and} \quad n \mid (a-b) $$
Since $m$ and $n$ are coprime and they both divide the integer $a-b$, their product $m \cdot n$ must also divide $a-b$. This is a fundamental property stemming from the fact that for coprime integers, if $m \mid k$ and $n \mid k$, then $mn \mid k$. Thus, we have:
$$ m \cdot n \mid (a-b) $$
By the definition of congruence, this is equivalent to $a \equiv b \pmod{m \cdot n}$.

($\Leftarrow$) For the other direction, assume that $a \equiv b \pmod{m \cdot n}$. By definition, this means that $m \cdot n$ divides $a-b$.
$$ m \cdot n \mid (a-b) $$
Since $m$ is a factor of $m \cdot n$, it must be that $m$ also divides $a-b$. This implies that $a \equiv b \pmod m$.
Similarly, since $n$ is a factor of $m \cdot n$, it must be that $n$ also divides $a-b$. This implies that $a \equiv b \pmod n$.
Thus, we have shown that $a \equiv b \pmod m$ and $a \equiv b \pmod n$, which completes the proof.