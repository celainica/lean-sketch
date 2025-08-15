**Theorem: Fermat's Little Theorem.** For any prime number $p$ and any integer $n$ coprime to $p$, we have the congruence
$$ n^{p-1} \equiv 1 \pmod p $$

---

**Lemma 1:** For a finite field $\mathbb{Z}_p$ where $p$ is a prime, any non-zero element $a \in \mathbb{Z}_p$ satisfies the equation $a^{p-1} = 1$.

*Proof.* The set of non-zero elements of the finite field $\mathbb{Z}_p$, denoted $(\mathbb{Z}_p)^\times$, forms a multiplicative group of order $p-1$. By Lagrange's theorem, the order of any element of a finite group divides the order of the group. Therefore, for any $a \in (\mathbb{Z}_p)^\times$, we have $a^{p-1} = 1$, where $1$ is the multiplicative identity in $\mathbb{Z}_p$.

---

**Proof of Theorem:**

Let $p$ be a prime number and $n$ be an integer. We are given that $n$ is coprime to $p$. Our goal is to prove that $n^{p-1} \equiv 1 \pmod p$.

The statement $n^{p-1} \equiv 1 \pmod p$ is, by definition, equivalent to the statement that the residue classes of $n^{p-1}$ and $1$ are equal in the ring of integers modulo $p$, denoted $\mathbb{Z}_p$. We write this as $[n^{p-1}] = [1]$ in $\mathbb{Z}_p$.

The condition that $n$ is coprime to $p$ means that $p$ does not divide $n$. In the context of modular arithmetic, this is equivalent to saying that the residue class of $n$ modulo $p$, $[n]$, is not the zero element in $\mathbb{Z}_p$. That is, $[n] \neq [0]$.

Since $\mathbb{Z}_p$ is a field (a consequence of $p$ being prime), every non-zero element is a unit. Thus, we can apply Lemma 1 to the non-zero element $[n] \in \mathbb{Z}_p$. The lemma gives us:
$$[n]^{p-1} = [1]$$
The rules of modular arithmetic state that $[n]^{p-1} = [n^{p-1}]$. Therefore, we have:
$$[n^{p-1}] = [1]$$
Translating this equality in $\mathbb{Z}_p$ back into the language of integer congruences, we obtain:
$$n^{p-1} \equiv 1 \pmod p$$
This completes the proof.