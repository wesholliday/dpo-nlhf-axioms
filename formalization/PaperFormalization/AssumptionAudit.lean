import PaperFormalization.PaperStatements

namespace PaperFormalization

/-!
Reviewer-facing assumption audit.

The `#print axioms` commands below are intentionally kept in the Lean artifact:
they let a reviewer ask Lean which axioms each paper-facing wrapper depends on.
No project-specific mathematical axiom is expected.  Lean/mathlib's standard
logical axioms (such as propositional extensionality, quotient soundness, and
classical choice) may still appear.
-/

#print axioms PaperStatements.BTProp
#print axioms PaperStatements.BTProp_existence
#print axioms PaperStatements.BTProp_profile
#print axioms PaperStatements.DPOasRTBT
#print axioms PaperStatements.DPOasRTBT_profile
#print axioms PaperStatements.DPOasRTBT_profile_selectedBT
#print axioms PaperStatements.DPOasRTBT_profile_addVoter
#print axioms PaperStatements.DPOasRTBT_profile_addVoter_selectedBT
#print axioms PaperStatements.Anderson
#print axioms PaperStatements.BIPOandPB
#print axioms PaperStatements.IPOandPB
#print axioms PaperStatements.IPOremark_population
#print axioms PaperStatements.IPOremark_population_pair
#print axioms PaperStatements.«nlhf-existence»
#print axioms PaperStatements.«nlhf-existence-diagonal»
#print axioms PaperStatements.«nlhf-existence-fixed-point»
#print axioms PaperStatements.«nlhf-existence-cbar»
#print axioms PaperStatements.«nlhf-existence-weak-profile»
#print axioms PaperStatements.MaxLottProp
#print axioms PaperStatements.MaxLottProp_limit
#print axioms PaperStatements.PBPM
#print axioms PaperStatements.PBPM_strict
#print axioms PaperStatements.RTBTPM
#print axioms PaperStatements.RTBTPM_profile
#print axioms PaperStatements.NLHFmono
#print axioms PaperStatements.NLHFmono_margin_score_bundle
#print axioms PaperStatements.NLHFmono_actual_profile_positive_clauses
#print axioms PaperStatements.NLHFmono_actual_linear_profile_converse_witness
#print axioms PaperStatements.NLHFmono_profile_all
#print axioms PaperStatements.NLHFmono_actual_transitive_profile_converse_witness
#print axioms PaperStatements.NLHFmono_finite_weak_order_score_representation
#print axioms PaperStatements.NLHFmono_finite_linear_order_score_representation
#print axioms PaperStatements.NLHFmono_profile_improvements
#print axioms PaperStatements.NLHFmono_actual_linear_profile_voterwise_converse_witness
#print axioms PaperStatements.PBPPI_positive
#print axioms PaperStatements.PBPPI_negative
#print axioms PaperStatements.PBPPI
#print axioms PaperStatements.PBPPI_positive_strict
#print axioms PaperStatements.PBPPI_negative_strict
#print axioms PaperStatements.InvolveViolNLHF_positive
#print axioms PaperStatements.InvolveViolNLHF_negative
#print axioms PaperStatements.InvolveViolNLHF
#print axioms PaperStatements.InvolveViolRTBT_positive
#print axioms PaperStatements.InvolveViolRTBT_negative
#print axioms PaperStatements.InvolveViolRTBT
#print axioms PaperStatements.RTBTorder
#print axioms PaperStatements.RTBTorder_strict
#print axioms PaperStatements.RTBTorder_domain_abstract
#print axioms PaperStatements.RTBTorder_domain
#print axioms PaperStatements.NLHFcomm
#print axioms PaperStatements.NLHFcomm_domain
#print axioms PaperStatements.NLHFcomm_profile_witness
#print axioms PaperStatements.«nlhf-variational»
#print axioms PaperStatements.RTBT_extension
#print axioms PaperStatements.RTBT_extension_agrees
#print axioms PaperStatements.RTBT_extension_linear_domain
#print axioms PaperStatements.RTBT_extension_singleton

end PaperFormalization
