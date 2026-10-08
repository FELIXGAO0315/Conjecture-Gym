import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C130 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsTree) (hn1 : 2 * (G.maxDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0) :
    (Fintype.card V : ℤ) + (G.indepNum : ℤ) ≥ 3 := by
  have s1 : (G.edgeFinset.card : ℤ) ≥ 0 := by positivity
  have s2 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) = -1 := by
    have hw := tree_edges_int G hp1
    linarith [hw]
  have s3 : (Fintype.card V : ℤ) ≥ 1 := by linarith [s1, s2]
  have s4 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
    have hw := chi_ge_one_int G (by omega)
    linarith [hw]
  have s5 : (G.indepNum : ℤ) ≥ 1 := by
    have hw := alpha_ge_one_int G (by omega)
    linarith [hw]
  have s6 : 2 * (G.maxDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [hn1]
  have s7 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
    have hw := max_lt_card_int G (by omega)
    linarith [hw]
  have s8 : 2 * (Fintype.card V : ℤ) + 2 * (G.indepNum : ℤ) ≥ 5 := by linarith [s4, s5, s6, s7]
  have s9 : (Fintype.card V : ℤ) + (G.indepNum : ℤ) ≥ 3 := by have hr := s8; omega
  linarith [s9]
