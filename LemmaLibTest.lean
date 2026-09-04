import LemmaLib

/-!
This target checks that every library module contributes a declaration to the public API. A module
can compile while hiding all its declarations when it uses Lean's explicit module system without a
`public section`; importing the umbrella module must make these names available.
-/

#check sub_sub_nsmul_eq_sum_secondDifference
#check AddMonoidHom.map_eq_zero_of_add_eq_self
#check Polynomial.coeff_comp_neg_X
#check Asymptotics.isLittleO_weighted_sum_range_of_tendsto_zero
#check HasDerivAt.eq_zero_of_even
#check exists_eq_zero_mem_Ioo_of_mul_neg
#check Nat.choose_two_sub_choose_two_pred
#check Abelianization.of_mul_mul_inv
#check Subgroup.twoClosure
#check SemidirectProduct.normal_subgroupOf_range_inl
#check Matrix.transpose_mul_finTwo_alternating_mul
#check Matrix.dotProduct_mulVec_eq_zero_of_transpose_eq_neg
#check Matrix.det_vandermonde_exp_neg_ne_zero
#check Function.range_eq_fixedPoints_of_idempotent
#check MeasureTheory.integral_det_columnwise
#check DeBruijnNewman.H
#check DeBruijnNewman.H_ne_zero_of_lt_norm_f'
#check exists_strictMono_dist_ge
#check DeBruijnNewman.H_zero_eq_xi
#check DeBruijnNewman.H_eq_integral_H_zero
#check DeBruijnNewman.B_mul_f
#check DeBruijnNewman.prefactor_log_le
#check DeBruijnNewman.effectiveApproximation_of
#check DeBruijnNewman.rtnEstimate
#check DeBruijnNewman.effectiveApproximation_of_tail
#check Complex.integral_add_eq_integral
#check EulerMaclaurin.sum_eq_integral_add
#check Complex.Stirling.exists_Gamma_eq_sqrt_two_pi_mul_exp
#check Complex.mordell_one
#check Complex.integral_rsLine_sub_eq_of_pole
#check RiemannSiegel.rsIntegral_add_half
#check RiemannSiegel.differentiable_rsIntegral
#check Complex.integral_cpow_mul_exp_neg_mul_Ioi_of_re_pos
#check RiemannSiegel.rsIntegral_eq_zeta_sub
