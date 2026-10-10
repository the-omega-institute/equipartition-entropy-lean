# Lean certificates for the entropy-constrained equipartition replacement

This project accompanies the re-examination of Conjecture 3.22(ii) in arXiv:2607.07851v1 (I. D. Dinov et al.). Authors of this formalization: Haobo Ma and Wenlin Zhang.

This separate project certifies the finite Gibbs/relative-entropy core, its exact scalar equality conditions, the real 2×2 covariance bound and equality conditions, and an explicit fourth-harmonic probability law with **actual Cartesian covariance** (I_4). It also certifies the calculus and order implications needed for a monotone scalar inverse, with the analytic hypotheses explicit.

**The full continuous-density Theorem 4.2 and Corollary 5.1 are not claimed as Lean theorems here.** In particular, their conditional Gibbs identity, zero-KL almost-everywhere equality theorem, Bessel integral differentiation and complete parameter range have not been instantiated in this project. The distinction is between proved finite statements and hypotheses in the continuous reduction, not between numerical and symbolic approximations: all the statements listed below are proved by Lean.

## Versions

- Lean `leanprover/lean4:v4.33.0`, Mathlib `v4.33.0` (revision `db584cd6d46c92f209a44c0f1c829460d327499d`); all dependency revisions are pinned in `lake-manifest.json`.
- Build and print axioms with `./build.sh`. Every listed theorem depends only on `propext`, `Classical.choice` and `Quot.sound`.

## Finite relative entropy and Gibbs tilt

The names in this section have namespace prefix **`DinovLean.`** and are defined in `DinovLean/Gibbs.lean`.

For finite arrays, define

\[
L(p,q)=p\log(p/q)-p+q,\qquad
\operatorname{KL}_{\mathrm{fin}}(p\Vert q)=\sum_i p_i\log(p_i/q_i).
\]

Lean's real logarithm is defined at zero; every zero candidate probability has coefficient zero, agreeing with the usual entropy convention. References are strictly positive. The nonnegativity and equality statements for finite KL require both arrays to sum to one.

| Exact theorem name after the prefix | Plain mathematical statement |
| --- | --- |
| `klTerm_nonneg` | If (p\ge0,q>0), then (L(p,q)\ge0). |
| `klTerm_eq_zero_iff` | Under those hypotheses, (L(p,q)=0\iff p=q). |
| `finiteKL_eq_sum_klTerm` | For arrays of mass one, finite KL equals the sum of the nonnegative (L(p_i,q_i)). |
| `finiteKL_nonneg` | For normalized (p\ge0,q>0), finite KL is nonnegative. |
| `finiteKL_eq_zero_iff` | For those normalized arrays, finite KL is zero exactly when the arrays are equal. |

For any real statistic (T_i), strictly positive reference weights (r_i), nonempty finite index set and any real parameter (\lambda), define

\[
Z(\lambda)=\sum_i r_i e^{\lambda T_i},\qquad
q_{\lambda,i}=r_i e^{\lambda T_i}/Z(\lambda).
\]

The reference weights need not be normalized for the tilt identity; choose normalized reference weights when interpreting the reference as a probability law.

| Exact theorem name after the prefix | Plain mathematical statement |
| --- | --- |
| `partition_pos` | (Z(\lambda)>0). |
| `gibbs_pos` | Every (q_{\lambda,i}>0). |
| `gibbs_sum` | (sum_i q_{\lambda,i}=1). |
| `gibbs_log_ratio` | (log(q_{\lambda,i}/r_i)=\lambda T_i-\log Z(\lambda)). |
| `finite_gibbs_identity` | For any normalized (p\ge0), (operatorname{KL}_{\rm fin}(p\Vert q_\lambda)=\operatorname{KL}_{\rm fin}(p\Vert r)-\lambda\sum_i p_iT_i+\log Z). |
| `finite_gibbs_inequality` | (lambda\sum_i p_iT_i-\log Z\le\operatorname{KL}_{\rm fin}(p\Vert r)). |
| `finite_gibbs_equality_iff` | Equality in that inequality holds exactly when (p=q_\lambda). |

The conditional version uses finite action indices (j), finite phase indices (i), fixed action weights (w_j), normalized conditional candidates (p_{j,i}), and one **separate normalizer (Z_j) on each action fiber**. Define

\[
D=\sum_jw_j\operatorname{KL}_{\rm fin}(p_j\Vert q_{\lambda,j}),\quad
K=\sum_jw_j\operatorname{KL}_{\rm fin}(p_j\Vert r_j),\quad
a=\sum_jw_j\sum_i p_{j,i}T_{j,i},\quad B=\sum_jw_j\log Z_j.
\]

| Exact theorem name after the prefix | Plain mathematical statement |
| --- | --- |
| `conditional_gibbs_identity` | (D=K-\lambda a+B), for arbitrary real action weights. |
| `conditional_gibbs_nonneg` | (D\ge0) when every action weight is nonnegative. |
| `conditional_gibbs_eq_zero_iff` | When every action weight is strictly positive, (D=0) exactly when (p_j=q_{\lambda,j}) on every fiber. |

The explicit definition **`DinovLean.secondStatistic J θ α`** is
(T_{j,i}=J_j\cos(2(\theta_i-\alpha))). Substituting this definition in the three conditional theorems gives the finite second-harmonic statements, with a common parameter and one fixed orientation. Each conditional law has mass one, so choosing (sum_jw_j=1) gives a joint probability array with the unchanged action weights (w_j). Neither a quadrature approximation to the continuous law nor a certified passage from finite arrays to continuous densities is asserted.

## Scalar lower bound and equality

These names also have prefix **`DinovLean.`** and are in `DinovLean/Gibbs.lean`. They are the exact algebraic reduction specified in the verified analytic note.

Let the real inputs satisfy

\[
\lambda>0,\quad D\ge0,\quad K\le C,\quad
D=K-\lambda a+b,\quad C=\lambda m-b.
\]

| Exact theorem name after the prefix | Plain mathematical statement |
| --- | --- |
| `gibbs_gap_identity` | The last two identities imply (lambda(m-a)=(C-K)+D), without sign assumptions. |
| `gibbs_gap_bound` | With the stated signs, (a\le m). |
| `gibbs_gap_eq_iff` | (a=m\iff K=C\text{ and }D=0). |
| `area_antitone` | For (0\le a\le m), (sqrt{1-m^2}\le\sqrt{1-a^2}). |
| `area_eq_iff` | For (a,m\in[0,1]), equality of these areas is equivalent to (a=m). |
| `centered_lower_bound` | For (a,m\in[0,1]) and the stated Gibbs assumptions, the area bound holds, and area equality is equivalent to (K=C,D=0). |
| `entropy_gap_identity` | If additionally (S=S_{\max}-2K) and (s=S_{\max}-2C), then (lambda(m-a)=(S-s)/2+D). |

For the continuous theorem, the intended inputs are (a=|M[\phi]|), (m=m(\lambda_s)), (b=b(\lambda_s)), (C=c(\lambda_s)), and the integrated conditional relative entropy (D). Those identifications are inputs to this finite-real certificate. The entropy identities make (K=C) equivalent to (S=s). Identifying zero continuous (D) with almost-everywhere equality to a Gibbs density remains a measure-theoretic bridge.

## The 2×2 covariance inequality

Names have prefix **`DinovLean.`** and are in `DinovLean/Covariance.lean`. Define

\[
\Sigma=\begin{pmatrix}v_q&c\\c&v_p\end{pmatrix}.
\]

The main bounds assume (v_q,v_p\ge0) and (det\Sigma\ge0), the scalar conditions supplied by a positive semidefinite covariance matrix. They are explicit hypotheses, not unverified axioms.

| Exact theorem name after the prefix | Plain mathematical statement |
| --- | --- |
| `block_det` | (det\Sigma=v_qv_p-c^2). |
| `block_trace_gap` | ((v_q+v_p)^2-4\det\Sigma=(v_q-v_p)^2+4c^2). |
| `covariance_trace_bound` | (sqrt{\det\Sigma}\le(v_q+v_p)/2). |
| `covariance_trace_eq_iff` | Equality holds exactly when (v_q=v_p,c=0). |
| `covariance_energy_bound` | If (v_q+v_p=2\eta-(\mu_q^2+\mu_p^2)), then (sqrt{\det\Sigma}\le\eta). |
| `covariance_energy_eq_iff` | Equality with (\eta) holds exactly when (\mu_q=\mu_p=0) and (Sigma=\eta I_2). |
| `second_harmonic_block_det` | (det\begin{pmatrix}1-x&y\\y&1+x\end{pmatrix}=1-(x^2+y^2)). |

This certifies the covariance upper bound and equality condition in the reflection's Proposition 2.1. It does not prove the general Williamson/Bhatia–Jain lower bound for an arbitrary covariance or symplectic orbit.

## Fourth-harmonic witness: an actual law

All names below have prefix **`DinovLean.Fourth.`**. The angular measure is ordinary Lebesgue measure restricted to ((-pi,\pi]); the action measure is Lebesgue measure restricted to ((0,\infty)). Thus the circle is represented by a fundamental interval. Put

\[
\phi_4(\theta)=\frac{1+\tfrac12\cos4\theta}{2\pi},\qquad
f(\theta,J)=\phi_4(\theta)e^{-J},\qquad
(q,p)=(\sqrt{2J}\sin\theta,\sqrt{2J}\cos\theta).
\]

`oneLaw` is the genuine measure with density (f). `torusLaw` is its product with itself. `law` is the **Cartesian pushforward** of that product by the displayed coordinate map. `covariance` uses Mathlib's actual `ProbabilityTheory.covariance`; its entries are not prescribed as inputs.

The angular certificates in `DinovLean/Angular4.lean` are:

| Exact theorem name after the prefix | Plain mathematical statement |
| --- | --- |
| `phi_continuous`, `phi_pos` | (phi_4) is continuous and strictly positive. |
| `phi_nonuniform` | (phi_4(0)\ne\phi_4(\pi/4)). |
| `phi_not_ae_uniform` | (phi_4) is not equal almost everywhere to ((2\pi)^{-1}). |
| `phi_polynomial` | (phi_4=[3/2+4\cos^4\theta-4\cos^2\theta]/(2\pi)). |
| `phi_mass` | (int\phi_4\,d\theta=1). |
| `cos_mean`, `sin_mean` | Both first angular moments vanish. |
| `cos_sq`, `sin_sq` | Each angular squared moment is (1/2). |
| `sin_cos` | The angular mixed moment is zero. |

These follow from exact trigonometric identities and interval integrals, including cosine-power integrals through degree six. They do not use numerical quadrature.

The realization certificates in `DinovLean/FourthHarmonic.lean` are:

| Exact theorem name after the prefix | Plain mathematical statement |
| --- | --- |
| `phase_mean`, `phase_product` | For the two functions (h_q=\sin,h_p=\cos), (int h_k\phi_4=0) and (int h_kh_l\phi_4=\delta_{kl}/2). |
| `density_measurable`, `density_pos`, `density_integrable`, `density_mass` | (f) is measurable, positive, integrable and has mass one. |
| `action_mass`, `action_integrable` | The exponential action density is integrable and has mass one. |
| `action_first_moment`, `action_first_integrable` | (Je^{-J}) is integrable and (int_0^\infty Je^{-J}dJ=1). |
| `one_probability` | The one-DOF measure is a probability measure (registered as an instance). |
| `action_fiber` | For every (J), (int f(\theta,J)d\theta=e^{-J}). |
| `expectation` | Expectations under `oneLaw` equal weighted integrals against its declared density. |
| `coordinate_mean` | Both actual one-DOF Cartesian means vanish. |
| `coordinate_product_ae` | The weighted coordinate product factors almost everywhere as (h_kh_l\phi_4\cdot2Je^{-J}). |
| `coordinate_product` | (E[Z_kZ_l]=\delta_{kl}). |
| `coordinate_square_integrable`, `coordinate_memLp` | Each squared coordinate is integrable; both one-DOF coordinates lie in (L^2). |
| `Z_measurable`, `Psi2_measurable` | The coordinates and the two-DOF pushforward map are measurable. |
| `one_covariance` | The actual one-DOF covariance is (I_2). |
| `torus_probability`, `law_probability` | Both the product law and its Cartesian pushforward are probability measures (instances). |
| `coord_comp` | Cartesian coordinate projections composed with the pushforward map are the declared action-angle coordinates. |
| `law_coordinate_memLp` | All four coordinates of the actual Cartesian law lie in (L^2). |
| `covariance_eq_identity` | The actual full Cartesian covariance is (I_4); independence proves the cross-DOF covariances vanish. |
| `covariance_posDef` | That actual covariance is positive definite. |
| `uncertainty_eq_one` | For each DOF, the square root of its actual covariance-block determinant is 1. |
| `williamson_certificate` | There exists (S) with (S^T\Omega S=\Omega) and (Sigma=S^T\operatorname{diag}(1,1,1,1)S), explicitly (S=I_4). |
| `problem317b_saturated` | For each DOF, (u_j=\min(1,1)=1), exact saturation at the certified symplectic frequencies. |

Here (Omega) is the standard interleaved symplectic form, with (q_j,p_j) adjacent. The frequencies **((1,1))** are certified by an actual Williamson factorization of the actual covariance. The project does not define a general symplectic-spectrum selection function or prove Williamson's theorem or spectral uniqueness for arbitrary positive definite matrices. This explicit factorization gives the requested witness spectrum without assuming the covariance as data.

Additional certificates in `DinovLean/WitnessProperties.lean` are:

| Exact theorem name after the prefix | Plain mathematical statement |
| --- | --- |
| `torusLaw_density` | The product measure is precisely the measure with density (F=f_1f_2) against the product base. |
| `joint_mass` | (int F=1). |
| `joint_action_fiber` | The double angular fiber integral of (F) is exactly (e^{-(J_1+J_2)}). |
| `phi_le_one`, `density_le_one` | (phi_4\le1) and (f\le1) for (J\ge0). |
| `density_log_decomposition` | (f\log f=(\phi_4\log\phi_4)e^{-J}-\phi_4Je^{-J}). |
| `density_log_integrable` | The one-DOF density times its log is absolutely integrable. |
| `joint_log_decomposition` | (F\log F=(f_1\log f_1)f_2+f_1(f_2\log f_2)). |
| `joint_log_integrable` | The two-DOF density times its log is absolutely integrable. |
| `actionAngleEntropy_nonneg` | The finite action-angle differential entropy (-\int F\log F) is nonnegative. |
| `omega_sq`, `omega_orthogonal` | (Omega^2=-I_4) and (Omega^T\Omega=I_4). |
| `fourth_harmonic_witness` | A bundled theorem combines probability, four (L^2) coordinates, nonuniform phase density modulo null sets, actual covariance (I_4), positive definiteness, the Williamson certificate, both uncertainties 1, and finite nonnegative action-angle entropy for this same realization. |

**Witness boundary.** The Cartesian law is formally connected to the covariance through its pushforward. The action marginal is certified through exact source fiber integrals. The project does not independently prove the polar Jacobian transport to a Cartesian Lebesgue density, the equality of action-angle and Cartesian differential entropies, or a generic joint-action pushforward identity. Accordingly, the finite nonnegative entropy certificate is explicitly for action-angle coordinates. No theorem here claims the full published predicate negating Conjecture 3.22(iii). The nonuniform density, actual covariance and saturation components of that witness are certified; the source's unit-Jacobian entropy bridge remains outside this small project's scope.

## Scalar inverse and lower-envelope monotonicity

Names have prefix **`DinovLean.`** and are in `DinovLean/ScalarInverse.lean`. Let (c(x)=xm(x)-b(x)).

| Exact theorem name after the prefix | Plain mathematical statement and assumptions |
| --- | --- |
| `cost_hasDerivAt` | If (b'(x)=m(x)) and (m'(x)=v), then (c'(x)=xv). |
| `cost_strictMonoOn` | If (c) is continuous on ([0,\infty)), the derivative identities hold for (x>0), and (v(x)>0), then (c) is strictly increasing on ([0,\infty)), including the endpoint where (c') may be zero. |
| `cost_inverse_unique` | Two nonnegative solutions to (c(x)=K) coincide if (c) is strictly increasing on that half-line. |
| `cost_inverse_strictMonoOn` | Every nonnegative right inverse (L) of such a (c) is strictly increasing for nonnegative budgets. |
| `cost_inverse_existsUnique` | If (c) is continuous and strictly increasing on ([0,\infty)), (c(0)=0), and for each (K\ge0) there is (B\ge0) with (K\le c(B)), then (c(x)=K) has a unique nonnegative solution. This uses the intermediate value theorem. |
| `floor_parameter_antitone` | The concentration (L((S_{\max}-s)/2)) is nonincreasing in (s\le S_{\max}). |
| `lower_envelope_monotone` | If (m) is additionally nonnegative and nondecreasing on the half-line, then (sqrt{1-m(L((S_{\max}-s)/2))^2}) is nondecreasing with the entropy floor. |

These results establish the calculus/order mechanism, not the Bessel-integral hypotheses of Lemma 4.1. In particular, this project does not prove (b'=m), positivity of the integrated Bessel variance, (m\to1), (c\to\infty), or the strict positive derivative (du_*/ds) for the reflection's actual functions. No numerical value or interval for (lambda_s), including (lambda_0), is certified.

## Remaining continuous theorem and effort estimate

A complete formalization of Theorem 4.2 still needs:

1. A measurable conditional-density class, finite conditional KL, normalization and the action-angle/Cartesian entropy bridge; the general weighted second-harmonic covariance identity and (|M|<1) from absolute continuity.
2. Conditional Gibbs normalization using the doubled circle and its (I_0(\lambda J)) normalizer, admissibility and finiteness for every finite parameter.
3. The integrated continuous Gibbs identity with all integrability conditions, and the zero-KL almost-everywhere equality case. This must enforce one common orientation, rather than an action-dependent rotation.
4. Dominated differentiation of (b,m,c), strict variance positivity, continuity at zero and the complete range. The elementary concentration and binary-KL proof in the verified analytic note can replace unformalized Bessel asymptotics.
5. Attainment, all density equality cases and the boundary floors (s=S_{\max}) and (s>S_{\max}).

Corollary 5.1 additionally needs the marginal KL/mutual-information decomposition, contraction/integrability, equality implying independence and the exact attainable pair region. Mathlib at this revision already contains `InformationTheory.KullbackLeibler.Basic`, `ChainRule` and `DataProcessing`; these should be reused, although they do not directly instantiate this conditional action-angle problem.

A planning estimate for an experienced Lean analyst is **four to eight working weeks** for the full continuous theorem and equality cases. Within that, the explicit witness's remaining Jacobian/entropy and action-pushforward bridges could plausibly take several days to one or two weeks with reuse of the earlier realization proof; the Bessel normalization, differentiation and full range are the main additional analytic work. Corollary 5.1 may add roughly one to two weeks depending on reuse of the KL chain-rule library. These are prospective estimates, not claims of completed validation or commitments to a deadline. The algebra and explicit witness moments requested here are already completed.

## Reproduction and kernel evidence

From this directory, run:

```sh
./build.sh
```

The script runs:

```sh
lake --no-cache --wfail build
lake env lean -j 2 -M 4096 -E warning DinovLean/Axioms.lean
python3 verify.py
```

**Concurrency detail:** this pinned Lake 5 does not accept `lake -j 2 build` (`unknown short option '-j'`). The local `lakefile.toml` instead supplies `moreLeanArgs = ["-j", "2", "-M", "4096"]`, so the actual Lean invocation in Lake's build uses the requested `-j 2`. The project's modules form a dependency chain, giving one active project compilation at a time. Existing dependency artifacts are reused; `--no-cache` disables remote cache downloading. On a fresh machine, install this toolchain and obtain the same pinned dependencies/cache first; a full uncached Mathlib rebuild is outside the small-project memory plan.

Every new proof is checked by Lean's kernel during elaboration. `DinovLean/Axioms.lean` has `#print axioms` for **all 90 public theorems and probability instances**; its complete output is saved in `evidence/axioms.log`. `verify.py` checks every inventory entry was actually printed and permits only `propext`, `Classical.choice` and `Quot.sound`. It rejects source proof placeholders, local axiom declarations, `native_decide` and `unsafe`. Imported Mathlib artifacts use the ordinary Lean import mechanism; this is not a separate trust-level-zero recheck of the entire Mathlib library.

Evidence files:

- `evidence/build.log`: final Lake build with warnings treated as errors.
- `evidence/axioms.log`: complete axiom dependency audit.
- `evidence/theorem-inventory.json`: every audited declaration's exact fully qualified name and source location.
- `evidence/verification.json`: machine-readable audit result, exact Mathlib revision, source hashes and upstream preservation result.
- `evidence/verification-run.log`: combined verification transcript.
- `evidence/reflection.txt`: extracted supplied reflection for source correspondence.

No email or Mail operation, git push, upstream source edit, CI change or publication was performed.
