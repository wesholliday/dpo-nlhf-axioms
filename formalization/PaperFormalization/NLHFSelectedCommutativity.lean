import PaperFormalization.NLHFExistence
import PaperFormalization.NLHFCommutativity

namespace PaperFormalization

/-- Proposition `NLHFcomm` for the selected strict-KL NLHF rule. -/
theorem selectedNLHFOfSionStrictKL_commutativity_violation
    (hexists : SionStrictKLFixedPointExistence (α := Fin 3))
    {τ : ℝ} (hτ : 0 < τ) :
    ViolatesCommutativity ((selectedNLHFOfSionStrictKL hexists) τ) :=
  NLHFcomm_violation_from_fixed_point_characterization hτ
    ((selectedNLHFOfSionStrictKL hexists) τ)
    (fun _ _ hM hρ =>
      selectedNLHFOfSionStrictKL_selection hexists hτ hM hρ)
    (fun _ _ _ hM hπ =>
      selectedNLHFOfSionStrictKL_isTheNLHF hexists hM hπ)

/-- Proposition `NLHFcomm` for the selected NLHF rule obtained from the proved
Sion specialization. -/
theorem selectedNLHF_commutativity_violation
    {τ : ℝ} (hτ : 0 < τ) :
    ViolatesCommutativity ((selectedNLHF (α := Fin 3)) τ) :=
  NLHFcomm_violation_from_fixed_point_characterization hτ
    ((selectedNLHF (α := Fin 3)) τ)
    (fun _ _ hM hρ => selectedNLHF_selection hτ hM hρ)
    (fun _ _ _ hM hπ => selectedNLHF_isTheNLHF hM hπ)

/-- Proposition `NLHFcomm` for the selected closed-Sion NLHF rule. -/
theorem selectedNLHFOfClosedSion_commutativity_violation
    (hsion : SionClosedSaddleExistence (α := Fin 3))
    {τ : ℝ} (hτ : 0 < τ) :
    ViolatesCommutativity ((selectedNLHFOfClosedSion hsion) τ) :=
  NLHFcomm_violation_from_fixed_point_characterization hτ
    ((selectedNLHFOfClosedSion hsion) τ)
    (fun _ _ hM hρ =>
      selectedNLHFOfClosedSion_selection hsion hτ hM hρ)
    (fun _ _ _ hM hπ =>
      selectedNLHFOfClosedSion_isTheNLHF hsion hM hπ)

end PaperFormalization
