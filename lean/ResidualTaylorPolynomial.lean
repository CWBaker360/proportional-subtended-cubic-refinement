import Mathlib
import ResidualTaylorPrereqs

namespace BakerTrisection

/--
The exact third-order Taylor polynomial of the
Baker 4:3 residual on any open interval
containing zero.
-/
theorem cubicResidual_taylor_polynomial
    (ε : ℝ) (hε : 0 < ε) (x : ℝ) :
    taylorWithinEval cubicResidual 3
      (Set.Ioo (-ε) ε) 0 x =
        -(7 / 384) * x ^ 3 := by

  let s : Set ℝ := Set.Ioo (-ε) ε

  have hopen : IsOpen s := by
    exact isOpen_Ioo

  have hzero : (0 : ℝ) ∈ s := by
    dsimp [s]
    constructor <;> linarith

  have hwithin (k : ℕ) :
      iteratedDerivWithin k cubicResidual s 0 =
        iteratedDeriv k cubicResidual 0 := by
    exact (iteratedDerivWithin_of_isOpen
      (n := k) (f := cubicResidual)
      (s := s) hopen) hzero

  have h0 :
      iteratedDerivWithin 0 cubicResidual s 0 = 0 := by
    rw [hwithin 0]
    simpa only [iteratedDeriv_zero] using
      cubicResidual_zero

  have h1 :
      iteratedDerivWithin 1 cubicResidual s 0 = 0 := by
    rw [hwithin 1, iteratedDeriv_one]
    exact cubicResidual_first_zero

  have h2 :
      iteratedDerivWithin 2 cubicResidual s 0 = 0 := by
    rw [hwithin 2]
    exact cubicResidual_second_zero

  have h3 :
      iteratedDerivWithin 3 cubicResidual s 0 =
        -(7 / 64) := by
    rw [hwithin 3]
    exact cubicResidual_third_zero

  change taylorWithinEval cubicResidual 3 s 0 x =
    -(7 / 384) * x ^ 3

  rw [taylor_within_apply]

  simp only [sub_zero]

  simp [Finset.sum_range_succ, h0, h1, h2, h3,
    smul_eq_mul]

  ring

end BakerTrisection

#check BakerTrisection.cubicResidual_taylor_polynomial
#print axioms BakerTrisection.cubicResidual_taylor_polynomial