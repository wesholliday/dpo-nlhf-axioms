"""Frozen references and immutable metadata for reproducible experiments."""
from __future__ import annotations

import hashlib
import importlib.metadata
import json
import platform
from pathlib import Path

import numpy as np
from scipy.special import logsumexp


def sha256_file(path: Path | str) -> str:
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def load_frozen_references(path: Path, labels: tuple[str, ...]) -> dict[str, dict]:
    references = {}
    for line in path.read_text().splitlines():
        if not line.strip():
            continue
        row = json.loads(line)
        key = row['prompt_id']
        if key in references:
            raise ValueError(f'Duplicate reference prompt: {key}')
        scores = np.array([row['response_logprobs'][x] for x in labels], dtype=float)
        if not np.isfinite(scores).all():
            raise ValueError(f'Nonfinite reference log probabilities: {key}')
        log_probs = scores-logsumexp(scores)
        p = np.array([row['rho'][x] for x in labels], dtype=float)
        if not np.isfinite(p).all() or np.any(p <= 0) or not np.isclose(p.sum(), 1, atol=1e-10, rtol=0):
            raise ValueError(f'Reference must be a full-support lottery: {key}')
        # Subnormal probabilities have coarse relative precision; compare in
        # probability space with a two-ULP-at-zero allowance, not log space.
        if not np.allclose(p, np.exp(log_probs), atol=2*np.nextafter(0.,1.), rtol=1e-12):
            raise ValueError(f'Cached probabilities do not match cached log scores: {key}')
        references[key] = dict(row, normalized_logprobs=dict(zip(labels, log_probs)))
    return references


def provenance(dataset: Path, reference_cache: Path | None,
               case_keys_file: Path | None, model_revision: str | None) -> dict:
    source_files = [
        'scripts/post_training/batch_profile_empirical_vs_theory.py',
        'scripts/post_training/train_coval_dpo.py',
        'scripts/post_training/train_coval_nash_md.py',
        'scripts/post_training/train_coval_nash_md_commutativity.py',
        'scripts/post_training/nash_md_loss.py',
        'scripts/post_training/experiment_provenance.py',
        'scripts/coval/profiles.py',
        'scripts/theory/nlhf_tie_normalization.py',
        'scripts/theory/search_strict_weak_positive_involvement.py',
    ]
    inputs = [dataset] + [p for p in [reference_cache, case_keys_file] if p is not None]
    return dict(
        schema_version=2, nlhf_gradient='exact_finite_slate_regularized_policy_gradient',
        model_revision=model_revision, python=platform.python_version(),
        packages={name: importlib.metadata.version(name)
                  for name in ['numpy', 'scipy', 'torch', 'transformers', 'peft']},
        inputs={str(p): sha256_file(p) for p in inputs},
        sources={str(p): sha256_file(p) for p in source_files},
    )


def ensure_metadata(path: Path, metadata: dict) -> None:
    """Resume only with exactly the same inputs, code, and configuration."""
    if path.exists():
        previous = json.loads(path.read_text())
        if previous != metadata:
            differing = sorted(k for k in previous.keys() | metadata.keys()
                               if previous.get(k) != metadata.get(k))
            raise ValueError(f'Refusing to mix experiment protocols at {path}; differing fields: {differing}. Use a new output/tag.')
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('x') as handle:
        json.dump(metadata, handle, indent=2, sort_keys=True, allow_nan=False)


def successful_case_keys(path: Path) -> set[str]:
    if not path.exists():
        return set()
    rows = {}
    for line in path.read_text().splitlines():
        if line.strip():
            row = json.loads(line)
            if not row.get('error'):
                key = row['case_key']
                if key in rows:
                    raise ValueError(f'Duplicate successful case in {path}: {key}')
                rows[key] = row
    return set(rows)
