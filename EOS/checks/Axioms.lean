import EOS
/-! Reproducible axiom check for every main theorem. Run: `cd EOS && lake env lean checks/Axioms.lean`.
Expected: each line `depends on axioms: [propext, Classical.choice, Quot.sound]`. -/
#print axioms EOS.coveredBy_of_grhBounds
#print axioms EOS.coveredBy_log_sq
#print axioms EOS.coveredByAsym_m_log_cube
#print axioms EOS.coveredBy_three_primes
#print axioms EOS.Buchstab.lemmaC
#print axioms EOS.Buchstab.lemmaC'
#print axioms EOS.Buchstab.buchstab_certificate
#print axioms EOS.eos_of_H4
#print axioms EOS.estermann_long
#print axioms EOS.estermann_long_log
#print axioms EOS.estermann_of_typeISifted
#print axioms EOS.SumTwoSquares.sumTwoSq_of_typeIHalf
#print axioms EOS.GRH.riemannHypothesis
#print axioms EOS.GRH_iff_forall
#print axioms EOS.LSeries_twist_vonMangoldt_eq_LFunction
#print axioms EOS.perron_cesaro_kernel
#print axioms EOS.psiCesaro_eq_verticalIntegral
#print axioms RectangleIntegral'_eq_sumResiduesIn
#print axioms Perron.formulaGtOne
#print axioms FinalBound
