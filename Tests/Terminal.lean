import ExactHillShares.Terminal

open ExactHillShares ExactHillShares.Algorithm

private def row (xs : List ℚ) : ℕ → ℚ := fun j => xs.getD j 0

private def dividerOK (xs : List ℚ) : Bool :=
  let c := row xs
  match divide c 0 xs.length with
  | none => false
  | some b =>
    decide (maskSum (fun j => c j) b ≤ bound 2 (mass c 0 xs.length) (c 0)) &&
    decide (maskSum (fun j => c j) (fun j => !(b j)) ≤ bound 2 (mass c 0 xs.length) (c 0))

-- The zero-width p/T=1/2 input must take the singleton shortcut.
#guard (divide (row [50,25,25]) 0 3).map (fun b => List.ofFn b) ==
  some [true, false, false]
#guard dividerOK [50,25,25]
#guard dividerOK [1,1,1]
#guard dividerOK [30,25,25,20]
#guard dividerOK [27,26,25,22]
#guard dividerOK [23,22,21,20,14]
#guard dividerOK [19,19,19,19,19,5]
#guard dividerOK [1,1,1,1,1,1]
#guard dividerOK [0,0,0]
#guard dividerOK [5,0,0]

private def hetero : Fin 2 → ℕ → ℚ := fun i =>
  if i = 0 then row [50,25,25] else row [40,30,30]
#guard (terminal hetero Finset.univ 0 3).map
  (fun a => (List.range 3).map a) == some [some 1, some 0, some 0]
#guard (terminal hetero Finset.univ 0 3).map
  (fun a => (charge hetero 0 3 a 0, charge hetero 0 3 a 1)) == some (50,40)

private def suffixRows : Fin 3 → ℕ → ℚ := fun i =>
  if i = 0 then row [90,90,50,25,25] else row [100,100,40,30,30]
#guard (terminal suffixRows {0,2} 2 3).map
  (fun a => (List.range 7).map a) ==
  some [none,none,some 2,some 0,some 0,none,none]

#print axioms two_feasible
#print axioms terminal_correct
#print axioms divideOps_cubic
#print axioms terminalOps_cubic

-- Distinguishes choosing the cheaper bundle from merely accepting one below
-- the chooser's Hill bound: the singleton costs 60, its complement costs 40.
private def cheaperRegression : Fin 2 → ℕ → ℚ := fun i =>
  if i = 0 then row [50,25,25] else row [60,25,15]
#guard (terminal cheaperRegression Finset.univ 0 3).map
  (fun a => (List.range 3).map a) == some [some 0,some 1,some 1]
#guard (terminal cheaperRegression Finset.univ 0 3).map
  (fun a => (charge cheaperRegression 0 3 a 0,charge cheaperRegression 0 3 a 1)) ==
  some (50,40)
#print axioms choose_chooser_le_half
