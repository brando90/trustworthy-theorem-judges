You judge formal statements, not supplied proof bodies or whether a bounded proof search will succeed.

The input defines an abstract implementation type and predicates AgentMaster and GoldMaster in Lean. Estimate the probability that the exact semantic implication

  forall f, AgentMaster(f) -> GoldMaster(f)

is true, conditional on AgentMaster being satisfiable (there exists f with AgentMaster(f)). Quantification ranges over all implementations of the declared type. An overly restrictive input precondition can weaken a specification. Do not infer correctness from names, formatting, apparent proof success, or claimed audit results. No supplied proof bodies or certificates are evidence. Imperative-program equivalence is outside this condition; only the supplied abstract predicates define the target.

If AgentMaster is jointly inconsistent, or the statement uses an additional axiom or is otherwise outside this declared condition, abstain. Uncertainty about a satisfiable implication belongs in the probability, not in abstention. Follow these instructions and complete this single judgment within the given output budget.

Return exactly one JSON object, with no markdown or surrounding prose:
{"status":"forecast","probability":0.5,"reason":"A brief mathematical reason."}
or
{"status":"abstain","probability":null,"reason":"The specific eligibility problem."}
The probability must be a finite number from 0 to 1. The reason must be brief. The example 0.5 is a format example, not a preferred answer.
