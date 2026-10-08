/-
PolyForge — graph domain Lean library (v1.1, stage 1).

The graph analogue of HexLemmas.lean: a small, self-proved lemma base on top of
Mathlib's graph theory, providing the inventory facts that are NOT already named
Mathlib lemmas, plus the ℕ∞→ℕ (`toNat`) finiteness/conversion forms the generated
conjectures are stated in.  No `sorry`, no axioms.

Invariant ↔ Lean (see domains/graph/inventory.py):
  n→Fintype.card V, m→edgeFinset.card, max_deg→maxDegree, min_deg→minDegree,
  chi→chromaticNumber.toNat, omega→cliqueNum, alpha→indepNum,
  tau→vertexCoverNum.toNat, diam→diam, radius→radius.toNat, girth→girth.
-/
import Mathlib

open Finset SimpleGraph

-- these lemmas share one `variable` block; some don't use every instance
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace PolyForge.Graph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ### max degree ≤ edges (inventory 5, from v1.0) -/

theorem maxDegree_le_card_edgeFinset :
    G.maxDegree ≤ G.edgeFinset.card :=
  G.maxDegree_le_of_forall_degree_le _ (fun v => G.degree_le_card_edgeFinset v)

/-! ### finiteness of the chromatic number -/

theorem chromaticNumber_ne_top : G.chromaticNumber ≠ ⊤ := by
  intro htop
  have h := G.chromaticNumber_le_card
  rw [htop] at h
  exact (ENat.natCast_ne_top (Fintype.card V)) (top_le_iff.mp h)

/-! ### positivity (n ≥ 1) : ω ≥ 1, α ≥ 1, χ ≥ 1 (inventory 8) -/

theorem one_le_cliqueNum [Nonempty V] : 1 ≤ G.cliqueNum := by
  have h := IsClique.card_le_cliqueNum (G := G) (t := {Classical.arbitrary V}) (by simp)
  simpa using h

theorem one_le_indepNum [Nonempty V] : 1 ≤ G.indepNum := by
  have h := IsIndepSet.card_le_indepNum (G := G) (t := {Classical.arbitrary V}) (by simp)
  simpa using h

/-- ω ≤ χ as a ℕ statement (inventory 1, toNat form). -/
theorem cliqueNum_le_chromaticNumber_toNat :
    G.cliqueNum ≤ G.chromaticNumber.toNat := by
  have h := ENat.toNat_le_toNat G.cliqueNum_le_chromaticNumber (chromaticNumber_ne_top G)
  simpa using h

/-- χ ≤ n as a ℕ statement (inventory 2, toNat form). -/
theorem chromaticNumber_toNat_le_card :
    G.chromaticNumber.toNat ≤ Fintype.card V := by
  have h := ENat.toNat_le_toNat G.chromaticNumber_le_card (ENat.natCast_ne_top (Fintype.card V))
  simpa using h

theorem one_le_chromaticNumber_toNat [Nonempty V] : 1 ≤ G.chromaticNumber.toNat :=
  (one_le_cliqueNum G).trans (cliqueNum_le_chromaticNumber_toNat G)

/-! ### Gallai identity α + τ = n (inventory 7) -/

theorem indepNum_add_vertexCoverNum_toNat :
    G.indepNum + G.vertexCoverNum.toNat = Fintype.card V := by
  classical
  -- a maximum independent set s (Finset) with #s = indepNum
  obtain ⟨s, hs⟩ := G.exists_isNIndepSet_indepNum
  have hs_indep : G.IsIndepSet ↑s := hs.isIndepSet
  have hs_card : s.card = G.indepNum := hs.card_eq
  -- a minimum vertex cover c (Set) with c.encard = vertexCoverNum
  obtain ⟨c, hc_enc, hc_cover⟩ := G.vertexCoverNum_exists
  -- τ = c.ncard
  have hc_ncard : c.ncard = G.vertexCoverNum.toNat := by
    rw [Set.ncard, hc_enc]
  -- cᶜ independent ⟹ #cᶜ ≤ indepNum
  have ind_c : G.IsIndepSet cᶜ := isIndepSet_compl_iff_isVertexCover.mpr hc_cover
  have hcompl_le : cᶜ.ncard ≤ G.indepNum := by
    have hle := IsIndepSet.card_le_indepNum (G := G) (t := cᶜ.toFinset)
      (by simpa [Set.coe_toFinset] using ind_c)
    simpa [Set.ncard_eq_toFinset_card'] using hle
  -- c and cᶜ partition the vertex set
  have hsum : c.ncard + cᶜ.ncard = Fintype.card V := by
    rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card]
  -- (↑s)ᶜ is a vertex cover ⟹ τ ≤ n − indepNum
  have cov_s : IsVertexCover G ((↑s : Set V)ᶜ) := isVertexCover_compl.mpr hs_indep
  have hsc_ncard : ((↑s : Set V)ᶜ).ncard = Fintype.card V - G.indepNum := by
    rw [Set.ncard_compl, Set.ncard_coe_finset, hs_card, Nat.card_eq_fintype_card]
  have h_upper : G.vertexCoverNum.toNat ≤ Fintype.card V - G.indepNum := by
    have h1 := cov_s.vertexCoverNum_le
    have hfin : ((↑s : Set V)ᶜ).encard ≠ ⊤ := (Set.toFinite _).encard_lt_top.ne
    have h2 := ENat.toNat_le_toNat h1 hfin
    rw [← Set.ncard] at h2
    rwa [hsc_ncard] at h2
  -- indepNum ≤ n
  have hind_le : G.indepNum ≤ Fintype.card V := by
    rw [← hs_card]; exact (s.card_le_univ).trans_eq (by simp)
  omega

/-! ### vertex cover : τ ≤ n − 1 (inventory 6), via Gallai + α ≥ 1 -/

theorem vertexCoverNum_toNat_le_card_sub_one [Nonempty V] :
    G.vertexCoverNum.toNat ≤ Fintype.card V - 1 := by
  have hg := indepNum_add_vertexCoverNum_toNat G
  have ha := one_le_indepNum G
  omega

/-! ### radius ≤ diam ≤ 2·radius (connected; inventory 9) -/

theorem radius_toNat_le_diam (h : G.Connected) :
    G.radius.toNat ≤ G.diam := by
  haveI := h.nonempty
  have hne : G.ediam ≠ ⊤ := SimpleGraph.connected_iff_ediam_ne_top.mp h
  have hle : G.radius ≤ G.ediam := SimpleGraph.radius_le_ediam
  simpa [SimpleGraph.diam] using ENat.toNat_le_toNat hle hne

theorem diam_le_two_mul_radius_toNat (h : G.Connected) :
    G.diam ≤ 2 * G.radius.toNat := by
  haveI := h.nonempty
  have hne : G.ediam ≠ ⊤ := SimpleGraph.connected_iff_ediam_ne_top.mp h
  have hrne : G.radius ≠ ⊤ :=
    fun hr => hne (SimpleGraph.ediam_eq_top_iff_radius_eq_top.mpr hr)
  have hcoe : (G.radius.toNat : ℕ∞) = G.radius := ENat.natCast_toNat hrne
  have hb : G.ediam ≤ ((2 * G.radius.toNat : ℕ) : ℕ∞) := by
    rw [Nat.cast_mul, Nat.cast_ofNat, hcoe]; exact G.ediam_le_two_mul_radius
  have ht := ENat.toNat_le_toNat hb (ENat.natCast_ne_top _)
  simpa [SimpleGraph.diam] using ht

/-! ### k-edge-connected ⟹ min_deg ≥ k (inventory 17) -/

theorem isEdgeConnected_le_minDegree [Nontrivial V] {k : ℕ}
    (h : G.IsEdgeConnected k) : k ≤ G.minDegree :=
  G.le_minDegree_of_forall_le_degree k (fun _ => h.le_degree)

end PolyForge.Graph
