# Figure reproduction

All 17 PDFs under `paper/figures/` are the final font-embedded exports. Their
exact hashes are in `results/figure_plot_data/FINAL_FIGURE_HASHES.json`.

```sh
pip install -r requirements-cpu.txt
# Install Ghostscript using your system's package manager, then:
python -m scripts.figures.rebuild_camera_ready --output-dir output/camera-ready-figures
```

The output directory must be empty. The wrapper uses the same rendering
functions and accepted saved data used for the camera-ready figures. It does
not train, recompute reference probabilities, solve targets, or repeat a
frequency search. PDF metadata/font-subset tags may differ across software
versions, so regenerated files need not have identical whole-file hashes.

| Figure family | Authoritative saved input |
|---|---|
| Main four-panel frequencies | `results/audits/replacement-figure-data-2026-10-28/T1/four_panel_plot_data.csv` |
| Unconditioned frequencies | Same directory, `T1/unconditioned_plot_data.csv` |
| Single-voter magnitudes | Same directory, `T1/single_voter_magnitudes.csv` |
| Commutativity magnitudes | Same directory, `T1/commutativity_magnitudes.csv` |
| Temperature-2 robustness (three figures) | Corresponding files in `T2/` |
| Nontrivial reference updates | Same directory, `nontrivial_reference_update_frequency.csv` |
| DPO agreement (three figures) | `results/empirical/dpo_rtbt/filtered_profile_sweeps/*.jsonl` |
| Joint DPO | `results/empirical/dpo_rtbt/joint_qwen25/run.json` |
| DPO involvement | `results/empirical/dpo_rtbt/involvement_witnesses/*/summary.csv` |
| Nash-MD agreement (three figures) | `results/empirical/nlhf_nashmd/filtered_profile_sweeps/*.jsonl` |
| Nash-MD commutativity | `results/figure_plot_data/nlhf_commutativity_single_profile_nashmd_agreement_plot_data.csv` |

The four frequency-table LaTeX fragments are in
`results/audits/replacement-figure-data-2026-10-28/T1/`:
`nlhf_conditioned_table.tex`, `nlhf_unconditioned_table.tex`,
`rtbt_conditioned_table.tex`, `rtbt_unconditioned_table.tex`.
Their numeric source CSVs are beside them. Integrate table labels with the
manuscript's labels rather than defining duplicate labels.

Individual original renderer entrypoints are retained for reference, but some
of their legacy default paths point to submitted summaries. Use the wrapper
above to regenerate the camera-ready set with the correct inputs and fonts.
