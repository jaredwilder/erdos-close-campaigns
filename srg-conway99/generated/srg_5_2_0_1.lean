import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.StronglyRegular

theorem oracle_srg_5_2_0_1 : (SimpleGraph.cycleGraph 5).IsSRGWith 5 2 0 1 := by
  constructor
  · intro v
    simpa using (SimpleGraph.cycleGraph_degree_three_le (n := 2) v)
  · intro v w h
    fin_cases v <;> fin_cases w <;> simp_all [SimpleGraph.cycleGraph_adj', SimpleGraph.commonNeighbors]
  · intro v w h
    fin_cases v <;> fin_cases w <;> simp_all [SimpleGraph.cycleGraph_adj', SimpleGraph.commonNeighbors]

