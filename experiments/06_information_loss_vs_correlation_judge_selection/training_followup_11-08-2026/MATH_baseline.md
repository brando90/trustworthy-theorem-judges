<!-- TLDR: A shared convex-mixture class permits weighted-PMF training and a globally optimal Pearson baseline without the old softmax scale-collapse mechanism. -->
# Same-class weighted-distance and Pearson training

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/06_information_loss_vs_correlation_judge_selection/training_followup_11-08-2026/MATH_baseline.md>

**TLDR:** Fit five nonnegative mixture weights summing to one, using the same cached probability vectors for both objectives. Weighted squared probability mass function (PMF) loss is a convex quadratic. Pearson correlation is solved through a nonnegative cone projection, with an exact best-vertex solution when every candidate correlation is nonpositive. This is a separately specified model class, not a repaired version of the old 36-coefficient softmax model.

## Shared model and target

For training artifact i and cached candidate j, let Q_ij be its six-category forecast and p_i the empirical human frequency vector on ratings 0–5. Both procedures fit the same model

    q_i(w) = sum_j w_j Q_ij,     w_j >= 0,     sum_j w_j = 1.

The weights are global across artifacts; the predictions remain paired with the same artifact. There is no target-dependent mapping at test time. The five-candidate simplex has four free weight coordinates, although correlated or duplicate candidates can reduce the identified dimension. Smoothing, if supplied by the calling protocol, is identical for both objectives. The module receives probability vectors as supplied; it does not add smoothing or use held-out ratings.

The weighted training objective is

    F(w) = (1/n) sum_i sum_r p_ir (q_ir(w) - p_ir)^2.

This uses each artifact's empirical human distribution. It is distinct from substituting one observed rating into both the weight and target, and is not claimed to be an unbiased proper per-observation score for an unknown population distribution.

## Weighted-distance optimizer and certificate

Write A_(i,r),j = sqrt(p_ir/n) Q_ijr and t_(i,r) = sqrt(p_ir/n) p_ir. Then F(w)=||Aw-t||² is convex. For each of the 31 nonempty candidate supports, solve the equality-constrained stationary equations by least squares, retain feasible nonnegative weights, and choose the smallest objective. A minimizer on the simplex has a support on which these equations hold. Singular faces have an optimal independent subface or a feasible stationary solution; all faces are enumerated.

For gradient g=2 Aᵀ(Aw-t), the simplex Frank–Wolfe gap

    gap = gᵀw - min_j g_j

is nonnegative in exact arithmetic and upper-bounds F(w)-min_v F(v). A reported success requires gap <= 1e-8. Thus solver termination is checked against an objective-specific global optimality certificate rather than an iterative optimizer's success flag.

## Pearson optimizer and proof

Let m_ij=sum_r (r/5) Q_ijr and y_i=sum_r (r/5) p_ir. Center each candidate column and the human mean:

    B_ij = m_ij - mean_i(m_ij),     b_i = y_i - mean_i(y_i).

For nonconstant outcomes, the objective is

    rho(w) = <Bw,b> / (||Bw|| ||b||).

Every nonzero nonnegative coefficient vector a corresponds to simplex weights a/sum(a), which preserve the direction of Ba. Therefore maximizing Pearson over simplex mixtures is equivalent to maximizing the angle agreement with b over the cone C={Ba:a>=0}, excluding zero vectors.

Let z be the Euclidean projection of b onto C, computed by nonnegative least squares. Projection onto a closed convex cone gives

    <b-z,z> = 0,     <b-z,v> <= 0 for every v in C.

If z is nonzero, then for every nonzero v in C,

    <b,v> <= <z,v> <= ||z|| ||v||.

Consequently rho(v)<=||z||/||b||, with equality for v=z. Normalizing the nonnegative coefficients of z gives a globally optimal simplex mixture. This proof addresses correlation itself; no probability loss or penalty is added to it.

The implementation normalizes nonconstant columns of B before projection, enumerates all nonempty supports, and solves each least-squares subproblem. It maps coefficients back to the original column scale before normalizing their sum. It checks nonnegative least-squares dual feasibility, complementarity, projection orthogonality and the identity between the achieved correlation and ||z||/||b||, using a 1e-8 numerical certificate tolerance. The mathematical result is exact; the implementation and certificates use floating-point tolerances.

### Nonpositive correlations

When every nonconstant column has <B_j,b><=0, projection returns zero. It would be wrong to normalize zero coefficients or call this optimum correlation zero. Let c=max_j corr(B_j,b)<=0. For any nonnegative coefficients,

    <sum_j a_j B_j,b> <= c ||b|| sum_j a_j ||B_j||
                       <= c ||b|| ||sum_j a_j B_j||.

The second inequality reverses the usual norm comparison because c is nonpositive. The best nonconstant single candidate therefore attains the global maximum, including the zero-correlation boundary case. The implementation selects that vertex deterministically.

### Constants, ties and unidentified probabilities

A constant human target or entirely constant candidate means makes Pearson undefined. The procedure returns uniform mixture weights and an explicit undefined status. The calling analysis retains these cells and must report them; undefined correlation is never silently scored as zero. Constant candidate columns are excluded from the nonconstant cone calculation.

The cone projection vector is unique, but its coefficient representation need not be. The resulting probability distribution is not identified by correlation alone: different distributions can have identical expected ratings, and adding a constant-mean component can preserve correlation. The prespecified convention is minimum nonzero support, then lexicographic candidate indices among numerical objective ties. It uses no held-out probability loss to resolve Pearson ties. This is an identification convention, not evidence that Pearson uniquely recovers human probabilities.

## Numerical settings and deterministic controls

`mixture_models.py` fixes feasibility tolerance 1e-10, relative linear-solve tolerance 1e-10, certificate tolerance 1e-8, relative objective-tie tolerance 1e-12, and constant centered-vector norm tolerance 1e-12. Candidate order is the incoming array order, which the run protocol must freeze. Both fits enumerate at most 31 faces for five candidates; there are no random starts, learning-rate choices or iterative convergence budgets.

`check_mixtures.py` uses synthetic data only, seed 20261108. It checks exact recovery of an interior three-candidate mixture, six independent two-candidate dense-grid comparisons for each objective, negative and zero correlations, duplicate candidates with the declared tie rule, constant targets, constant predictions, different distributions with identical means, and one constant candidate beside an informative candidate. The module does not open the empirical dataset.

## What this condition can establish

It compares training objectives within a shared, explicitly limited mixture class and removes the prior nonconvex softmax optimizer as a confound. It does not establish unrestricted language-model training, prompt optimization, fresh human validation, universal objective superiority or transfer to unseen solver/rater populations. Weighted softmax-head fitting, if run separately, must retain its separate model-class description and receipts.
