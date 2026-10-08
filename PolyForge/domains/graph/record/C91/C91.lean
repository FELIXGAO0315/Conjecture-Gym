import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C91 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsBipartite) (hn1 : (G.maxDegree : ℤ) - 2 * (G.indepNum : ℤ) ≥ 0) (hn2 : (Fintype.card V : ℤ) ≤ 4) :
    -(G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≤ -1 := by
  have s1 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by
    have hw := not_bipartite_chi_int G hp1
    linarith [hw]
  have s2 : (G.maxDegree : ℤ) - 2 * (G.indepNum : ℤ) ≥ 0 := by linarith [hn1]
  have s3 : -(Fintype.card V : ℤ) ≥ -4 := by linarith [hn2]
  have s4 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := chi_le_n_int G
    linarith [hw]
  have s5 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s4, s1]
  have s6 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
    have hw := max_lt_card_int G (by omega)
    linarith [hw]
  have s7 : -2 * (G.indepNum : ℤ) ≥ -3 := by linarith [s2, s3, s6]
  have s8 : -(G.indepNum : ℤ) ≥ -1 := by have hr := s7; omega
  have s9 : (G.chromaticNumber.toNat : ℤ) - 2 * (G.indepNum : ℤ) ≥ 1 := by linarith [s1, s8]
  linarith [s9]
