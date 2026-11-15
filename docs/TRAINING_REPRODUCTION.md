# Reproducing the reported training protocol

The paper uses historical training and same-protocol completion cases. The
package includes the source versions used for those experiments.
Generic parser defaults are not the paper settings; pass the explicit
flags below. Training is not required to regenerate figures from the saved
results. Direct all new outputs to a fresh directory under `output/`.

## Version and input selection

Run from the supplement root. `scripts/run_version.py` selects an immutable
source tree, leaves the supplement root as the working directory and forwards
arguments. It does not change any loss, seed or optimizer.

- `historical`: DPO, joint DPO, historical single-profile Nash-MD and all paper
  commutativity training. The historical solver is preserved in this tree;
  use the corrected root analysis for final targets/summaries.
- `completion_2026_11_01`: the 85 Nemo completions. Use only the single-profile
  batch entrypoint for these cases. Its unused captured commutativity module
  is not the one that produced the paper's commutativity runs.

The model revisions used for completion/reproduction are:

| Model | Hugging Face model | Revision |
|---|---|---|
| Qwen2.5 | `Qwen/Qwen2.5-7B` | `d149729398750b98c0af14eb82c78cfe92750796` |
| Qwen3 | `Qwen/Qwen3-8B-Base` | `49e3418fbbbca6ecbdf9608b4d22e5a407081db4` |
| Nemo | `mistralai/Mistral-Nemo-Base-2407` | `a4477a2f977929a969745b69bbd62e03043551a5` |

The historical scripts predate the `--model-revision` option: point them to a
local checkout of the intended revision. Hardware/software and RNG partition
can affect trajectories; source fidelity is not a promise of bitwise equality.

## DPO single-profile and joint training

The 154 / 167 / 199 single-profile cohorts are listed under `results/case_keys/`.
All use beta=0.1, 100 steps, seed 0, identity stripping, LoRA r=8, alpha=32,
dropout=0.05 and q_proj/v_proj. Qwen2.5 and Qwen3 use float16 and lr=5e-5;
Nemo uses float32 and lr=1e-5. Qwen3 and Nemo record gradient clipping 1.0;
Qwen2.5's historical metadata has no clipping key. DPO weight decay is 0.01.
The single-profile and joint trainers use AdamW's default, and the batch
runner's weight-decay argument defaults to 0.01. All DPO experiments use
full-batch updates. The Qwen3 metadata records `dpo_full_batch: true`.
The Qwen2.5 and Nemo metadata predate that field. Pass `--dpo-full-batch`
explicitly when using the batch runner or chunk orchestrator.

For example, the historical Qwen2.5 full-batch single-profile sweep is:

```sh
python scripts/run_version.py historical scripts.post_training.batch_profile_empirical_vs_theory \
  --dataset data/coval_comparisons.jsonl --blocks world,personal --rules dpo \
  --model local_models/qwen25_7b_bf16 --renderer qwen --identity-mode strip_identity \
  --device mps --dtype float16 --beta 0.1 --steps 100 --lr 5e-5 \
  --seed 0 --max-length 4096 --lora-r 8 --lora-alpha 32 --lora-dropout 0.05 \
  --target-modules q_proj,v_proj --dpo-full-batch --weight-decay 0.01 \
  --case-keys-file results/case_keys/qwen25_dpo.case_keys.txt \
  --output-root output/reproduction/dpo-qwen25
```

The joint Qwen2.5 run uses one shared adapter, 100 full-batch steps, lr=1e-5,
float16, clipping 1.0 and AdamW weight decay 0.01. It covers 154 profiles/129 distinct prompts, with
12,179 preference pairs. Use the historical
`train_coval_dpo_multi_profile.py` with those explicit flags, the Qwen2.5 DPO
case list and the settings recorded in
`results/empirical/dpo_rtbt/joint_qwen25/run.json`. It is not the same learning
rate as the individual Qwen2.5 runs.

## Historical single-profile Nash-MD

All three models use tau=0.01, float32, 300 steps, lr=3e-6, clipping 1.0,
weight decay 0, epsilon=1e-4, no epsilon decay, mixture coefficient 0,
LoRA r=8/alpha=32/dropout=0 on q_proj/v_proj, seed 0, max length 4096 and
identity stripping. Each run computes its own base-model reference; do not
substitute the profile-selection reference cache into the loss.

```sh
python scripts/run_version.py historical scripts.post_training.batch_profile_empirical_vs_theory \
  --dataset data/coval_comparisons.jsonl --blocks world,personal --rules nlhf \
  --model local_models/qwen25_7b_bf16 --renderer qwen --identity-mode strip_identity \
  --device mps --dtype float32 --tau 0.01 --steps 300 --lr 3e-6 \
  --nlhf-exploration-epsilon 0.0001 --nlhf-exploration-decay-steps 0 \
  --nlhf-mixture-coef 0 --nlhf-checkpoint-every 0 --seed 0 --max-length 4096 \
  --lora-r 8 --lora-alpha 32 --lora-dropout 0 --target-modules q_proj,v_proj \
  --weight-decay 0 --grad-clip 1.0 \
  --case-keys-file results/case_keys/qwen25_nlhf.case_keys.txt \
  --output-root output/reproduction/nlhf-qwen25
```

For historical Nemo use its model and `--renderer llama2 --fix-mistral-regex`.
For Qwen3 use its model, renderer qwen and the appropriate device. The single
recovered Qwen3 MPS case used checkpoint interval 50. Historical batches set
seed once; do not add `--reset-seed-per-case`. Final cohort membership lists
alone do not reconstruct the original shard order or RNG state.

## Nemo completion batches

The eight original H100 case lists are in
`code_versions/completion_2026_11_01/batches/gpu0.case_keys.txt` through `gpu7`.
Four cases encountered CUDA OOM and were completed in the separate M3 batch.
The final merged cohort retains 81 CUDA plus four MPS successes; it does not
count failed CUDA attempts as trained successes. The successful completion rows are in `results/empirical/nlhf_nashmd/completion85.jsonl`.
The published cohort includes the 85 successful completions.

One H100 batch can be reproduced with:

```sh
python scripts/run_version.py completion_2026_11_01 scripts.post_training.batch_profile_empirical_vs_theory \
  --dataset data/coval_comparisons.jsonl --blocks world,personal --rules nlhf \
  --model local_models/mistral_nemo_base_2407 \
  --model-revision a4477a2f977929a969745b69bbd62e03043551a5 \
  --device cuda --dtype float32 --renderer llama2 --identity-mode strip_identity \
  --tau 0.01 --steps 300 --lr 3e-6 --nlhf-exploration-epsilon 0.0001 \
  --nlhf-exploration-decay-steps 0 --nlhf-mixture-coef 0 --nlhf-checkpoint-every 0 \
  --seed 0 --no-reset-seed-per-case --max-length 4096 \
  --lora-r 8 --lora-alpha 32 --lora-dropout 0 --target-modules q_proj,v_proj \
  --weight-decay 0 --grad-clip 1.0 --cpu-threads 4 \
  --case-keys-file code_versions/completion_2026_11_01/batches/gpu0.case_keys.txt \
  --output-root output/reproduction/nemo-gpu0
```

Each original H100 batch ran as one persistent process on one GPU, with seed
0 set once. The M3 fallback used the same scientific modules and parameters,
`--device mps` and `batches/mps.case_keys.txt`; its recorded MPS memory setting
is in `completion_batches.json`. The completion runs did not enable
`--fix-mistral-regex` and did not pass `--reference-cache`.
The published results and batch metadata identify the successful runs.

## Nash-MD commutativity

Use `historical scripts.post_training.train_coval_nash_md_commutativity`,
never the unused completion-tree version. For each order, the source creates
AdamW once before its stage loop. Stage 2 uses the learned stage-1 policy as
reference and carries the optimizer state forward. Explicit flags are:

```
--dtype float32 --tau 0.01 --mixture-coef 0 \
--exploration-epsilon 0.0001 --exploration-decay-steps 0 \
--steps-per-stage 300 --lr 3e-6 --seed 0 --max-length 4096 \
--grad-clip 1.0 --weight-decay 0 --lora-r 8 --lora-alpha 32 \
--lora-dropout 0 --target-modules q_proj,v_proj --identity-mode strip_identity
```

The 502 run records in
`results/audits/commutativity-training-2026-10-28/all_current_documented_runs.jsonl.gz`
contain the profile identifiers, both stage ranking lists, order, reference
probabilities, settings and learned probabilities. Supply those recorded
rankings using `--rankings-left-json` and `--rankings-right-json`, along with the
recorded prompt, block and order. Qwen uses renderer qwen; Nemo uses renderer
llama2 and `--fix-mistral-regex`. Both orders of each documented pair are
retained even when the final corrected predicted magnitude is below 0.01.
