import Mathlib.Combinatorics.SimpleGraph.StronglyRegular

theorem oracle_srg_complete_5 : (⊤ : SimpleGraph (Fin 5)).IsSRGWith 5 4 3 0 :=
  SimpleGraph.IsSRGWith.top
