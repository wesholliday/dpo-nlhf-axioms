# Results manifest

`empirical/` contains the figure cohorts and recorded settings. Single-profile
Nash-MD counts are Qwen2.5 215, Qwen3 221 and Nemo 279. DPO counts are 154,
167 and 199. The commutativity figure contains 249 of 251 documented pairs,
with the 502-run record in `audits/commutativity-training-2026-10-28/`.

`audits/numerical-2026-10-28/` and
`audits/commutativity-batched-2026-10-28/` contain the numerical outputs and
summaries. `audits/replacement-figure-data-2026-10-28/` contains their figure
and table inputs. `reference_distributions/` contains the base-model reference
probabilities, and `case_keys/` identifies the single-profile cohorts.

See `docs/FIGURES.md` for the input-to-figure mapping and
`docs/CODE_AND_RESULT_PROVENANCE.md` for the methods and source versions.
