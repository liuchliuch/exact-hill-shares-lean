import ExactHillShares.TrimmedSubsetSum

open ExactHillShares.Trimmed

#eval solve [1/4, 1/4, 1/4, 1/4] (7/16) (9/16)
#eval solve [2, 3, 5] 4 5
#eval solve [0, 2, 3, 0, 5] 4 5
#eval (run true (1/10) 10 [2, 3, 5]).size
#eval (run false (1/10) 10 [2, 3, 5]).size
#eval (entries (run true (1/10) 10 [2, 3, 5])).map State.value
#eval (entries (run false (1/10) 10 [2, 3, 5])).map State.value

#print axioms run_sound
#print axioms run_approximates
#print axioms final_hit
#print axioms solve_correct
#print axioms solve_two_bin
#print axioms polynomial_complexity
#print axioms solveOps_cubic
#print axioms finite_solve_correct
#print axioms trim_extremal
#print axioms solvePeak_quadratic
#print axioms paper_bucket_bound
