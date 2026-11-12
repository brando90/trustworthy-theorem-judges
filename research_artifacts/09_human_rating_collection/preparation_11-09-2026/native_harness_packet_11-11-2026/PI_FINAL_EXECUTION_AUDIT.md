# Native Pi generation: final audit

**TLDR:** All 25 original Pi attempts are terminal; 0 required-path artifacts were captured. Every attempt and failure is preserved; no task was retried.

Native Pi 1.5.2 used `gemini-3.8-flash` with high thinking under the frozen per-cell caps: 40 generation requests including generation retries, 1,800 seconds, 65,536 input tokens, 16,384 output tokens, and $0.75. Token-counting preflights are additional HTTP calls, outside the generation-request counter.

Valid-cohort conservative cost: $10.91049525, comprising $9.69398325 completed-usage upper bounds and $1.21651200 unresolved request reservations. Invalid environment pilot: $0.72042450, separately excluded. Combined: $11.63091975 against the $20 ceiling. Cache discounts are ignored; this is not an invoice.

[Full evidence and per-task receipts](PI_FINAL_EXECUTION_AUDIT.json). The separate [output-path diagnostic](PI_OUTPUT_CAPTURE_DIAGNOSTIC.md) explains why the conclusion concerns required-path submissions. The two recovered host-wrapper cases retain their original conversations, deadlines, native sessions and explicit incident provenance.

| Task | Captured file | Generation requests | Terminal causes |
|---|---:|---:|---|
| `realcode_set__20_html_escape` | missing | 40 | Provider request cap reached |
| `easy_set__23_is_prime` | missing | 6 | URLError |
| `security_set__security_6858__vulnerabilities__93_unsafeappentitlements` | missing | 5 | HTTPError |
| `security_set__security_6858__vulnerabilities__129_unsafetorhiddenservice` | missing | 4 | TimeoutError |
| `easy_set__41_duplicate_chars` | missing | 4 | HTTP503 before response; HTTPError |
| `security_set__security_6858__vulnerabilities__75_unsafecerthostname` | missing | 3 | HTTP503 before response; HTTPError |
| `humaneval_set__humaneval_35_max_element` | missing | 39 | Original wall-clock cap |
| `cs_set__topological_sort` | missing | 40 | Provider request cap reached; Host-wrapper-loss incident; original Docker conversation recovered without restart |
| `humaneval_set__humaneval_39_prime_fib` | missing | 40 | Provider request cap reached; Host-wrapper-loss incident; original Docker conversation recovered without restart |
| `realcode_set__23_base32` | missing | 19 | Native output-length stop / provider MAX_TOKENS |
| `humaneval_set__humaneval_15_string_sequence` | missing | 40 | Provider request cap reached |
| `cs_set__counting_sort` | missing | 40 | Provider request cap reached |
| `easy_set__16_myfactorial` | missing | 15 | Input token cap exceeded |
| `humaneval_set__humaneval_14_all_prefixes` | missing | 40 | Provider request cap reached |
| `easy_set__20_mysumdigits` | missing | 29 | Cell dollar cap cannot admit next request |
| `humaneval_set__humaneval_4_mean_absolute_deviation` | missing | 30 | HTTP503 before response; Cell dollar cap cannot admit next request |
| `cs_set__heapsort_algorithm` | missing | 28 | HTTPError |
| `easy_set__19_mypower` | missing | 14 | HTTPError |
| `security_set__security_6858__vulnerabilities__95_unsafetlsdowngrade` | missing | 40 | Provider request cap reached |
| `security_set__security_6858__safe__125_unsafetpmhash_safe` | missing | 36 | Cell dollar cap cannot admit next request |
| `cs_set__edit_distance` | missing | 16 | Input token cap exceeded |
| `realcode_set__21_shlex_quote` | missing | 40 | Provider request cap reached |
| `realcode_set__31_statistics_quantiles` | missing | 33 | Cell dollar cap cannot admit next request |
| `realcode_set__28_statistics_median_low` | missing | 35 | Cell dollar cap cannot admit next request |
| `cs_set__heap_sort` | missing | 34 | Cell dollar cap cannot admit next request |
