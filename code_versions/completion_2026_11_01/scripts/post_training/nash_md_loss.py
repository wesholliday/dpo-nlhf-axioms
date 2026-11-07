"""Historical uniform-floor Nash-MD score weights for the isolated85 replication."""
import torch
import torch.nn.functional as F


def finite_slate_nash_md_loss(log_policy, ref_log_policy, preference_probs, tau,
                              mixture_coef=0.0, exploration_epsilon=0.0):
    if not 0 <= exploration_epsilon < 1:
        raise ValueError('Require exploration_epsilon in [0, 1)')
    if not 0 <= mixture_coef <= 1 or tau <= 0:
        raise ValueError('Require tau > 0 and mixture_coef in [0, 1]')
    with torch.no_grad():
        policy = log_policy.detach().exp()
        mixture_logits = mixture_coef * ref_log_policy + (1-mixture_coef) * log_policy.detach()
        mixture = F.softmax(mixture_logits, dim=0)
        expected_advantage = (preference_probs-.5).matmul(mixture)
        coefficient = tau * (log_policy.detach()-ref_log_policy) - expected_advantage
    score_weights = policy if exploration_epsilon == 0 else ((1-exploration_epsilon)*policy
                    + exploration_epsilon*torch.full_like(policy, 1.0/policy.numel()))
    return torch.sum(score_weights*coefficient*log_policy)
