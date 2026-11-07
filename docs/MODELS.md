# Models And Hardware

## Base Models

The experiments use base, non-instruction-tuned models where available:

- Qwen2.5: `Qwen/Qwen2.5-7B`
- Qwen3: `Qwen/Qwen3-8B-Base`
- Mistral-Nemo: `mistralai/Mistral-Nemo-Base-2407`

The repository does not include model checkpoints. Download them into `local_models/`:

```zsh
hf download Qwen/Qwen2.5-7B --revision d149729398750b98c0af14eb82c78cfe92750796 --local-dir local_models/qwen25_7b_bf16
hf download Qwen/Qwen3-8B-Base --revision 49e3418fbbbca6ecbdf9608b4d22e5a407081db4 --local-dir local_models/qwen3_8b_base
hf download mistralai/Mistral-Nemo-Base-2407 --revision a4477a2f977929a969745b69bbd62e03043551a5 --local-dir local_models/mistral_nemo_base_2407
```

## Reference Distribution Protocol

For each CoVal prompt, we score the four candidate responses under the base model. If `s_x` is the sequence log probability assigned to candidate response `x`, the reference distribution is

```text
rho(x) = exp(s_x) / sum_y exp(s_y).
```

The reference-distribution caches included with this repository are
PyTorch-derived from the Hugging Face checkpoints listed above. For
Mistral-Nemo, aggregate frequency analyses use the complete float32 cache
`results/reference_distributions/nemo_pytorch_rho_strip_identity_float32.jsonl`.
The five Nemo worked examples use the earlier float16 reference evaluations
in `results/reference_distributions/worked_examples/nemo_pytorch_rho_strip_identity.jsonl`.
That file contains 635 saved prompts, including all five example prompts;
its accompanying original metadata records float16 evaluation on MPS.
Use the full-precision saved probabilities when reproducing the examples.

## Prompt Normalization

The CoVal prompts contain a sentence identifying the assistant as ChatGPT. The current protocol removes that vendor-specific identity sentence before scoring or training. In scripts this is `--identity-mode strip_identity`.

## Software

Observed local software versions:

- Python virtual environment with PyTorch `2.11.0`
- Transformers `5.6.0`
- PEFT `0.19.1`
- NumPy `2.4.4`
- SciPy `1.17.1`
- Matplotlib `3.10.8`

See `requirements.txt`.

## Hardware

Local runs used Apple Silicon machines with MPS where available. The empirical
checks require machines with sufficient memory to load the relevant base model
and LoRA adapter; larger-memory Apple Silicon desktops were used for the
longest local sweeps, and a laptop-class Apple Silicon machine was used for
selected auxiliary runs.

Long macOS runs should be launched under `caffeinate`; see `scripts/orchestration/run_with_caffeinate.sh`.
