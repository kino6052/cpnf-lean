I agree with all three exclusions. I would add a test for “identity of a step”: **what must the step have emitted before it is allowed to count as a repetition?** The ordinary sieve step emits a survivor. It does not promise to emit a twin. Repeating that step licenses another survivor, not another occurrence of every recognizable pattern among survivors.

My recommendation is a **finite-return principle** with a checkable output condition. It fits the ontology, has an unconditional first theorem on your actual trace, and leaves a precisely located open obligation for twins.

### Fixing the statement before choosing a principle

Write \(c_k=\texttt{certify}\ k\), \(h_k=\texttt{head}\ k\), and \(D(k)=\texttt{Direct}\ k\). Thus \(D(k)\) says that the next ordinary survivor is one of the two members at the current head. This is an observation of the original generator; it does not feed anything back into it. Your `prime_of_direct` and `direct_of_twin` establish both directions of the bridge: a direct event gives a real twin, and every real twin of positive index occurs at a direct event with exactly that head.

There are two logical strengths worth keeping separate:
\[
 L_D=\neg\exists K\,\forall k\ge K\,\neg D(k),\qquad
 P_D=\forall K\,\exists k\ge K\,D(k).
\]
The first is the literal “never reaches a stage after which no twin is ever certified.” The second is positive productivity: given a stage, there is a finite return with an output. Constructively \(P_D\) implies \(L_D\); the reverse is not a rule of intuitionistic logic. Classically they agree. The source states `OftenDirect` with a bound on the **head**, not the clock, but for positive productivity the two bounds are interchangeable: `head_unbounded` and `head_mono` turn a clock-cofinal supply into a head-cofinal one; a direct event with head \(>h_K\) must occur after \(K\).

One implementation qualification matters. `TwinCertifiedAt` is a least-element readout without Algorithm 2’s history \(T\); the two are not definitionally the same. Nor is `Direct` defined as a successful search in a window. If the claim is specifically about **Algorithm 2’s log**, there is a separate classical bridge. Each positive logged index is genuine: all primes through the window’s square-root cutoff have been included. Conversely, suppose there is a last success (or none; take the empty-history maximum as zero). Completion to its fixed finite target terminates, and thereafter every failed search advances by exactly one ordinary prime. For any sufficiently late genuine twin with lower member \(p\), this tail therefore searches with largest blocker \(y\) equal to the prime immediately preceding \(p\). Bertrand’s postulate gives \(p<2y\), hence \(p+2\le y^2\) for \(y\ge3\). Neither member is blocked, the index is in the window, and it is not in the finite log. The search must succeed, a contradiction. This is a **tail argument**; it does not assume that every stage succeeds or that the two implementations log identical sequences.

### Four principles, ranked by fit

Here **(a)** means a verdict on the actual twin statement, not merely an implication with an undischarged premise; **(b)** means a changed generator; **(c)** means changed meanings. “No verdict” reports what the rule delivers here, not a formal independence claim.

| Rank | Principle — what it says | (a) | (b) | (c) |
|---|---|---|---|---|
| 1 | **Certified finite return:** if a routine takes each recognized state through a positive finite segment of the actual trace, emits a specified event, and returns to the recognized kind, it can be iterated on demand. | No verdict for twins | No | No |
| 2 | **Faithful finite recognition:** a repeated finite label licenses replay of its event pattern if the label determines both the next label and the current event bit. | No verdict for twins | No | No |
| 3 | **Least-witness choice:** for a decidable stage test known to succeed somewhere after each input stage, searching in order selects a next successful stage. | No verdict for twins | No | No |
| 4 | **Markov reflection for trace search:** for a decidable event test, impossibility of an entirely unsuccessful tail search licenses existence of a finite success on that tail. | No verdict; upgrades \(L_D\) to \(P_D\) *if given* \(L_D\) | No | No |

**1. Finite return.** The proof obligation is about the whole finite segment, not the shape of its endpoints alone. A segment that returns to “valid sieve state” without a twin is a valid return for the ordinary sieve and an invalid return for a twin emitter. Requiring an event inside the segment also rules out declaring success by returning to the same state in zero steps. The rule is sound by finite iteration; it needs no new arithmetic axiom.

**2. Faithful recognition.** Precisely, take a finite label set \(Q\), a label \(q(k)\in Q\), and maps \(f:Q\to Q\), \(e:Q\to\{0,1\}\). Prove \(q(k+1)=f(q(k))\) and \(e(q(k))=1\) exactly at the proposed events. If \(q(i)=q(j)\) with \(i<j\), induction gives equal labels at all corresponding future offsets. An event in \([i,j)\) then repeats; an event-free cycle instead certifies silence. Pigeonhole supplies a repeat, **not** event fidelity or a favorable cycle.

This identifies the specific failure of the paper’s fixed-modulus recognition. For a fresh prime \(p>3\) coprime to \(M_0\), representatives \(r+tM_0\) of **one** old label run through *all* residues modulo \(p\). Two lifts modulo \(pM_0\) over that label are hit; the other \(p-2\) are not. The new hit bit is not a function of the old label. Finiteness of \(R_0\) thus gives no finite subcover of its integer representatives. Determinism of the blocker generator does nothing to repair this loss of information.

**3. Least-witness choice.** Given \(P_D\), test \(D(K),D(K+1),\ldots\) and stop at the first success. That is a named implementation, with \(P_D\) as its termination proof. Each individual test is finite: even the unwindowed head search has the factorial bound from `admissible_factorial`. So neither a choice of scheduler nor a more generous fairness policy is missing. Running every test eventually guarantees discovery of a later twin **if there is one**. It cannot make a false test pass.

**4. Markov reflection.** The exact extra rule is \(\neg\neg\exists j\,E(j)\Rightarrow\exists j\,E(j)\) for decidable \(E\). It is sound in the standard classical interpretation, though not mandatory in a constructive foundation. For each \(K\), \(L_D\) gives \(\neg\neg\exists j\,D(K+j)\), so the rule bridges the two formulations above without changing either. It supplies no argument for \(L_D\). In particular, “no finite prefix proves permanent silence” is **not** the required double negation: even a machine programmed to emit nothing has finite prefixes compatible, when viewed only as output data, with a later success.

### The negative result one can actually establish

**Transfer, not independence.** Let \(S\) be a proposed process calculus, and let \(A\) be an ordinary mathematical theory in which its finite traces can be interpreted. Suppose the interpretation uses the actual sieve, translates the claimed event faithfully, and validates every axiom and inference rule of \(S\). Then a derivation in \(S\) of actual twin non-stagnation translates into a derivation in \(A\) of its arithmetic counterpart. The proof is induction on the derivation: translate the axioms, then apply the validity of each translated rule. For classical \(A\), the counterpart is the ordinary twin-prime conjecture, by the bridge above. The same transfer applies to a negative verdict.

This does **not** prove that no natural axiom can decide twins, or even that a particular established theory cannot already decide them. “Natural” is not a formal class of axioms, and the arithmetic correspondence is not an independence theorem. What it rules out is a **discount in proof strength** from a faithful change of presentation alone. If a proposed axiom is justified only by saying it is consistent, there is a further problem: consistency does not certify truth on the intended trace.

The sources give useful calibration points. `OftenDirect` and `CofinalScoreEnergy` as axioms are relabelings, by the supplied equivalences. `CofinalScoreMass` is a sufficient arithmetic hypothesis; the source proves the implication, not its premise or its converse. `DicksonTwoPositive` would give **(a) yes, (b) no, (c) no** if assumed. It is a general conjecture about linear forms, not a shifted copy and not merely new notation for twins. But its soundness on the actual numbers is unestablished. I would present it as a conditional, not as a sound process principle.

### What I would build: returns with receipts

For a decidable event predicate \(E\) on ordinary stages, write
\[
 K\xRightarrow[E]{\,j\,}J
 \quad\text{iff}\quad K\le j<J\ \text{ and }\ E(j).
\]
The receipt is the finite trace from \(K\) to \(J\) with marked event \(j\); no new number or sieve transition is introduced. A return routine on a stage predicate \(I\) must, on input \(K\) satisfying \(I(K)\), supply such \(j,J\) and evidence for \(I(J)\). Finite recursion then constructs as many successive receipts as requested, with distinct, strictly increasing event stages.

**First theorem — bounded return for actual head changes.** Put \(E(k):=\texttt{Dies}\ k\), meaning \(h_k<h_{k+1}\), and take \(I\) to be all ordinary stages. Then
\[
 \forall K\ \exists j,\qquad
 K\xRightarrow[E]{\,j\,}j+1,\qquad
 h_j=h_K,\qquad
 j+1\le \max\{K,\,6h_K-1+1\}.
\]
Indeed, `head_escapes` says the head is already larger than \(h_K\) at the displayed upper bound. Scan from \(K+1\) to that bound for the first larger head. Its predecessor \(j\) has head exactly \(h_K\) by monotonicity and minimality, and the step at \(j\) changes it. This constructs the receipt by bounded search. `dies_iff` even identifies its cause: the new blocker divides one of the old head’s two members.

That last distinction is the ledger I would put in the paper: **the actual trace productively emits head changes; it is open whether it productively emits direct head changes.** The former has a bounded, repeatable step with a receipt. For the latter one must show that arbitrarily late a killing divisor **is a member**, rather than a proper divisor. That is where the process notation earns its keep: it identifies exactly which event the loop proves, without granting it credit for a different one.
