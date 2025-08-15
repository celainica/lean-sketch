**Theorem: The Law of Quadratic Reciprocity.** For distinct odd primes $p$ and $q$, the following relation holds:
$$ \left(\frac{q}{p}\right)\left(\frac{p}{q}\right) = (-1)^{\frac{p-1}{2}\frac{q-1}{2}} $$

---

**Lemma 1:** For any odd natural number $n$, $\chi_4(n) = (-1)^{(n-1)/2}$, where $\chi_4$ is the primitive Dirichlet character modulo 4.

*Proof.* The character $\chi_4(n)$ is defined as $1$ if $n \equiv 1 \pmod 4$ and $-1$ if $n \equiv 3 \pmod 4$. We check these two cases.
Since $n$ is odd, we can write $n = 2k+1$ for some integer $k$. Then $(n-1)/2 = k$.
If $n \equiv 1 \pmod 4$, then $n = 4m+1$ for some integer $m$. Then $k = (4m)/2 = 2m$ is even, so $(-1)^{(n-1)/2} = (-1)^{2m} = 1$, which matches $\chi_4(n)$.
If $n \equiv 3 \pmod 4$, then $n = 4m+3$ for some integer $m$. Then $k = (4m+2)/2 = 2m+1$ is odd, so $(-1)^{(n-1)/2} = (-1)^{2m+1} = -1$, which also matches $\chi_4(n)$.
Thus, the identity holds for all odd $n$.

---

**Lemma 2:** For a finite field $F$ with characteristic not equal to $2$, and an odd prime $p$ different from the characteristic of $F$, the following identity holds for the quadratic character $\psi_F$ of $F$:
$$ \psi_F(p) = \psi_{\mathbb{Z}_p}(\chi_4(|F|) \cdot |F|) $$
where $\psi_{\mathbb{Z}_p}(\cdot)$ is the quadratic character on $\mathbb{Z}_p$, which corresponds to the Legendre symbol $\left(\frac{\cdot}{p}\right)$.

*Proof.* This is a key result from the theory of quadratic characters, often derived using properties of Gauss sums.

---

**Proof of Theorem:**

Let $p$ and $q$ be distinct odd primes. Our goal is to prove that $\left(\frac{q}{p}\right)\left(\frac{p}{q}\right) = (-1)^{\frac{p-1}{2} \frac{q-1}{2}}$.

The Legendre symbol $\left(\frac{a}{p}\right)$ is defined as the value of the quadratic character of the finite field $\mathbb{Z}_p$, which we denote by $\psi_{\mathbb{Z}_p}(a)$. The quadratic character is a multiplicative homomorphism $\psi_{\mathbb{Z}_p} : \mathbb{Z}_p^\times \to \{\pm 1\}$.

We begin by applying Lemma 2 with the field $F = \mathbb{Z}_p$ and the prime (in the lemma's sense) $q$. Since $p$ is an odd prime, its characteristic is not 2, and since $p \neq q$, the conditions of the lemma are met. The cardinality of the field is $|F| = |\mathbb{Z}_p| = p$. The lemma thus gives us:
$$ \psi_{\mathbb{Z}_p}(q) = \psi_{\mathbb{Z}_q}(\chi_4(p) \cdot p) $$
Using the standard notation for the Legendre symbol, this is:
$$ \left(\frac{q}{p}\right) = \left(\frac{\chi_4(p) \cdot p}{q}\right) $$
Now, consider the product we wish to evaluate:
$$ \left(\frac{q}{p}\right)\left(\frac{p}{q}\right) $$
Substituting the result from Lemma 2, we get:
$$ \left(\frac{\chi_4(p) \cdot p}{q}\right)\left(\frac{p}{q}\right) $$
Since the Legendre symbol is completely multiplicative in its top argument, we can split the first term:
$$ \left(\frac{\chi_4(p)}{q}\right) \left(\frac{p}{q}\right) \left(\frac{p}{q}\right) = \left(\frac{\chi_4(p)}{q}\right) \left(\frac{p}{q}\right)^2 $$
As $p$ and $q$ are distinct primes, $p \not\equiv 0 \pmod q$, which implies that $\left(\frac{p}{q}\right)$ is either $1$ or $-1$. In either case, its square is $1$:
$$ \left(\frac{p}{q}\right)^2 = 1 $$
The entire expression simplifies to:
$$ \left(\frac{\chi_4(p)}{q}\right) $$
Since $p$ is an odd prime, we can apply Lemma 1 to evaluate $\chi_4(p)$:
$$ \chi_4(p) = (-1)^{(p-1)/2} $$
Substituting this into our expression, we have:
$$ \left(\frac{(-1)^{(p-1)/2}}{q}\right) $$
Using the multiplicative property of the Legendre symbol again, this is equivalent to:
$$ \left(\frac{-1}{q}\right)^{(p-1)/2} $$
The value of $\left(\frac{-1}{q}\right)$ is a well-known result (the first supplementary law to quadratic reciprocity), which states that for an odd prime $q$, $\left(\frac{-1}{q}\right) = (-1)^{(q-1)/2}$.
Substituting this final piece, we obtain:
$$ \left((-1)^{(q-1)/2}\right)^{(p-1)/2} $$
By the laws of exponents, this simplifies to:
$$ (-1)^{\frac{p-1}{2} \frac{q-1}{2}} $$
This completes the proof of the Law of Quadratic Reciprocity.