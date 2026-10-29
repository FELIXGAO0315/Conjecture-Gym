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

/-! ### ℤ wrapper lemmas (v1.1 §I.2)

One per inventory entry, stating the relation in ℤ over the invariant
expressions (n→card, m→edgeFinset.card, max_deg/min_deg→max/minDegree,
chi→chromaticNumber.toNat, omega→cliqueNum, alpha→indepNum,
tau→vertexCoverNum.toNat, diam→diam, radius→radius.toNat, girth→girth).  The
graph formalizer `have`-introduces exactly these and closes with linarith/omega.
Property hypotheses are stated in the v1.1 §I.3 forms; positivity/nontriviality
are supplied as card bounds (`1 ≤ card` / `2 ≤ card`) and the Nonempty/Nontrivial
instances are derived inside. -/

-- 1
theorem omega_le_chi_int : (G.cliqueNum : ℤ) ≤ (G.chromaticNumber.toNat : ℤ) := by
  exact_mod_cast cliqueNum_le_chromaticNumber_toNat G
-- 2
theorem chi_le_n_int : (G.chromaticNumber.toNat : ℤ) ≤ (Fintype.card V : ℤ) := by
  exact_mod_cast chromaticNumber_toNat_le_card G
-- 3
theorem min_le_max_int : (G.minDegree : ℤ) ≤ (G.maxDegree : ℤ) := by
  exact_mod_cast G.minDegree_le_maxDegree
-- 4
theorem max_lt_card_int (hn : 1 ≤ Fintype.card V) :
    (G.maxDegree : ℤ) ≤ (Fintype.card V : ℤ) - 1 := by
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have h := G.maxDegree_lt_card_verts
  omega
-- 5
theorem max_le_edges_int : (G.maxDegree : ℤ) ≤ (G.edgeFinset.card : ℤ) := by
  exact_mod_cast maxDegree_le_card_edgeFinset G
-- 6
theorem tau_le_card_sub_one_int (hn : 1 ≤ Fintype.card V) :
    (G.vertexCoverNum.toNat : ℤ) ≤ (Fintype.card V : ℤ) - 1 := by
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have h := vertexCoverNum_toNat_le_card_sub_one G
  omega
-- 7
theorem gallai_int :
    (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = (Fintype.card V : ℤ) := by
  exact_mod_cast indepNum_add_vertexCoverNum_toNat G
-- 8a
theorem chi_ge_one_int (hn : 1 ≤ Fintype.card V) : (1 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ) := by
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  exact_mod_cast one_le_chromaticNumber_toNat G
-- 8b
theorem omega_ge_one_int (hn : 1 ≤ Fintype.card V) : (1 : ℤ) ≤ (G.cliqueNum : ℤ) := by
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  exact_mod_cast one_le_cliqueNum G
-- 8c
theorem alpha_ge_one_int (hn : 1 ≤ Fintype.card V) : (1 : ℤ) ≤ (G.indepNum : ℤ) := by
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  exact_mod_cast one_le_indepNum G
-- 9a
theorem radius_le_diam_int (h : G.Connected) :
    (G.radius.toNat : ℤ) ≤ (G.diam : ℤ) := by
  exact_mod_cast radius_toNat_le_diam G h
-- 9b
theorem diam_le_two_radius_int (h : G.Connected) :
    (G.diam : ℤ) ≤ 2 * (G.radius.toNat : ℤ) := by
  have := diam_le_two_mul_radius_toNat G h; omega
-- 10
theorem tree_edges_int (h : G.IsTree) :
    (G.edgeFinset.card : ℤ) = (Fintype.card V : ℤ) - 1 := by
  have := h.card_edgeFinset; omega
-- 11
theorem tree_min_deg_int (h : G.IsTree) (hn : 2 ≤ Fintype.card V) :
    (G.minDegree : ℤ) = 1 := by
  haveI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have := h.minDegree_eq_one_of_nontrivial; omega
-- 12
theorem acyclic_chi_int (h : G.IsAcyclic) : (G.chromaticNumber.toNat : ℤ) ≤ 2 := by
  have h2 := ENat.toNat_le_toNat h.chromaticNumber_le_two (by simp)
  simp only [ENat.toNat_ofNat] at h2
  exact_mod_cast h2
-- 13
theorem girth_le_diam_int (h : G.Connected) (_hc : ¬ G.IsAcyclic) :
    (G.girth : ℤ) ≤ 2 * (G.diam : ℤ) + 1 := by
  haveI := h.nonempty
  have hne : G.ediam ≠ ⊤ := SimpleGraph.connected_iff_ediam_ne_top.mp h
  have := G.girth_le_two_mul_diam_add_one hne; omega
-- 14
theorem girth_ge_three_int (hc : ¬ G.IsAcyclic) : (3 : ℤ) ≤ (G.girth : ℤ) := by
  have := G.three_le_girth hc; omega
-- 15
theorem connected_min_deg_int (h : G.Connected) (hn : 2 ≤ Fintype.card V) :
    (1 : ℤ) ≤ (G.minDegree : ℤ) := by
  haveI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have := h.preconnected.minDegree_pos_of_nontrivial; omega
-- 16a
theorem regular_max_int {d : ℕ} (h : G.IsRegularOfDegree d) (hn : 1 ≤ Fintype.card V) :
    (G.maxDegree : ℤ) = (d : ℤ) := by
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have := h.maxDegree_eq; omega
-- 16b
theorem regular_min_int {d : ℕ} (h : G.IsRegularOfDegree d) (hn : 1 ≤ Fintype.card V) :
    (G.minDegree : ℤ) = (d : ℤ) := by
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have := h.minDegree_eq; omega
-- 17
theorem edge_conn_min_deg_int {k : ℕ} (h : G.IsEdgeConnected k) (hn : 2 ≤ Fintype.card V) :
    (k : ℤ) ≤ (G.minDegree : ℤ) := by
  haveI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have := isEdgeConnected_le_minDegree G h; omega
-- bipartite ⟺ chi ≤ 2 (property premise → numeric chi fact, §II.3)
theorem bipartite_chi_int (h : G.IsBipartite) : (G.chromaticNumber.toNat : ℤ) ≤ 2 := by
  have h2 := ENat.toNat_le_toNat (chromaticNumber_le_two_iff_isBipartite.mpr h) (by simp)
  simp only [ENat.toNat_ofNat] at h2
  exact_mod_cast h2
theorem not_bipartite_chi_int (h : ¬ G.IsBipartite) : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ) := by
  have hne := chromaticNumber_ne_top G
  have h2 : ¬ (G.chromaticNumber ≤ 2) := fun hc => h (chromaticNumber_le_two_iff_isBipartite.mp hc)
  have h3 : (2 : ℕ∞) < G.chromaticNumber := not_le.mp h2
  rw [← ENat.natCast_toNat hne] at h3
  have h4 : 2 < G.chromaticNumber.toNat := by exact_mod_cast h3
  omega

/-! ### v1.1.1 elementary facts -/

-- connected + nontrivial ⟹ diam ≥ 1
theorem one_le_diam_of_connected (h : G.Connected) (hn : 2 ≤ Fintype.card V) :
    1 ≤ G.diam := by
  haveI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  haveI := h.nonempty
  have hne : G.ediam ≠ ⊤ := SimpleGraph.connected_iff_ediam_ne_top.mp h
  have h1 : 1 ≤ G.ediam := Order.one_le_iff_ne_zero.mpr G.ediam_ne_zero
  have := ENat.toNat_le_toNat h1 hne
  simpa [SimpleGraph.diam] using this

-- connected + nontrivial ⟹ radius ≥ 1
theorem one_le_radius_of_connected (h : G.Connected) (hn : 2 ≤ Fintype.card V) :
    1 ≤ G.radius.toNat := by
  haveI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  haveI := h.nonempty
  have hne : G.ediam ≠ ⊤ := SimpleGraph.connected_iff_ediam_ne_top.mp h
  have hrne : G.radius ≠ ⊤ :=
    fun hr => hne (SimpleGraph.ediam_eq_top_iff_radius_eq_top.mpr hr)
  have hz : G.radius ≠ 0 := by
    intro heq
    rw [SimpleGraph.radius_eq_zero_iff] at heq
    exact (not_subsingleton_iff_nontrivial.mpr ‹Nontrivial V›) heq.2
  have h1 : 1 ≤ G.radius := Order.one_le_iff_ne_zero.mpr hz
  have := ENat.toNat_le_toNat h1 hrne
  simpa using this

-- connected ⟹ m ≥ n − 1
theorem card_edgeFinset_ge_card_sub_one (h : G.Connected) :
    Fintype.card V ≤ G.edgeFinset.card + 1 := by
  have h1 := h.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card] at h1
  have hE : Nat.card (↑G.edgeSet) = G.edgeFinset.card := by
    rw [Nat.card_eq_fintype_card, ← Set.toFinset_card]; rfl
  rw [hE] at h1; exact h1

/-! ### v1.1.1 ℤ wrappers -/

theorem diam_ge_one_int (h : G.Connected) (hn : 2 ≤ Fintype.card V) :
    (1 : ℤ) ≤ (G.diam : ℤ) := by
  have := one_le_diam_of_connected G h hn; omega

theorem radius_ge_one_int (h : G.Connected) (hn : 2 ≤ Fintype.card V) :
    (1 : ℤ) ≤ (G.radius.toNat : ℤ) := by
  have := one_le_radius_of_connected G h hn; omega

theorem connected_edges_int (h : G.Connected) :
    (Fintype.card V : ℤ) - 1 ≤ (G.edgeFinset.card : ℤ) := by
  have := card_edgeFinset_ge_card_sub_one G h; omega

/-! ### v1.1.2 §I: nonempty-unconditional ℤ wrappers (graphs assumed [Nonempty V]) -/

theorem card_ge_one_int [Nonempty V] : (1 : ℤ) ≤ (Fintype.card V : ℤ) := by
  have h0 : 1 ≤ Fintype.card V := Fintype.card_pos
  exact_mod_cast h0

theorem max_lt_card_int' [Nonempty V] :
    (G.maxDegree : ℤ) ≤ (Fintype.card V : ℤ) - 1 := by
  have := G.maxDegree_lt_card_verts; omega

theorem tau_le_card_sub_one_int' [Nonempty V] :
    (G.vertexCoverNum.toNat : ℤ) ≤ (Fintype.card V : ℤ) - 1 := by
  have := vertexCoverNum_toNat_le_card_sub_one G
  have h1 : 1 ≤ Fintype.card V := Fintype.card_pos
  omega

theorem chi_ge_one_int' [Nonempty V] : (1 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ) := by
  exact_mod_cast one_le_chromaticNumber_toNat G

theorem omega_ge_one_int' [Nonempty V] : (1 : ℤ) ≤ (G.cliqueNum : ℤ) := by
  exact_mod_cast one_le_cliqueNum G

theorem alpha_ge_one_int' [Nonempty V] : (1 : ℤ) ≤ (G.indepNum : ℤ) := by
  exact_mod_cast one_le_indepNum G

theorem regular_max_int' [Nonempty V] {d : ℕ} (h : G.IsRegularOfDegree d) :
    (G.maxDegree : ℤ) = (d : ℤ) := by
  have := h.maxDegree_eq; omega

theorem regular_min_int' [Nonempty V] {d : ℕ} (h : G.IsRegularOfDegree d) :
    (G.minDegree : ℤ) = (d : ℤ) := by
  have := h.minDegree_eq; omega

/-! ### v1.1.2 §II: elementary facts -/

-- alpha ≤ n  (independence number ≤ vertices)
theorem indepNum_le_card : G.indepNum ≤ Fintype.card V := by
  have h : Gᶜ.cliqueNum = G.indepNum := cliqueNum_compl
  have h2 := Gᶜ.cliqueNum_le_natCard
  rw [Nat.card_eq_fintype_card, h] at h2; exact h2

theorem alpha_le_card_int : (G.indepNum : ℤ) ≤ (Fintype.card V : ℤ) := by
  have := indepNum_le_card G; omega

-- omega ≤ n  (clique number ≤ vertices)
theorem omega_le_card_int : (G.cliqueNum : ℤ) ≤ (Fintype.card V : ℤ) := by
  have := G.cliqueNum_le_natCard; rw [Nat.card_eq_fintype_card] at this; omega

-- tau ≤ m  (vertex-cover number ≤ edges)
theorem vertexCoverNum_toNat_le_edges : G.vertexCoverNum.toNat ≤ G.edgeFinset.card := by
  have h := G.vertexCoverNum_le_encard_edgeSet
  have henc : G.edgeSet.encard = (G.edgeFinset.card : ℕ∞) := by
    rw [Set.encard_eq_coe_toFinset_card]; rfl
  rw [henc] at h
  exact (ENat.toNat_le_toNat h (ENat.natCast_ne_top _)).trans_eq (ENat.toNat_coe _)

theorem tau_le_edges_int : (G.vertexCoverNum.toNat : ℤ) ≤ (G.edgeFinset.card : ℤ) := by
  have := vertexCoverNum_toNat_le_edges G; omega

-- has_cycle ⟹ nontrivial  (a graph with a cycle has ≥ 2 vertices)
theorem hasCycle_two_le_card (h : ¬ G.IsAcyclic) : 2 ≤ Fintype.card V := by
  by_contra hc
  haveI : Subsingleton V := Fintype.card_le_one_iff_subsingleton.mp (by omega)
  have hbot : G = ⊥ := by
    ext a b; simp only [bot_adj, iff_false]
    exact fun hab => hab.ne (Subsingleton.elim a b)
  exact h (hbot ▸ isAcyclic_bot)

theorem hasCycle_two_le_card_int (h : ¬ G.IsAcyclic) : (2 : ℤ) ≤ (Fintype.card V : ℤ) := by
  have := hasCycle_two_le_card G h; omega

-- is_connected ∧ has_cycle ⟹ m ≥ n
theorem conn_cycle_card_le_edges (hconn : G.Connected) (hcyc : ¬ G.IsAcyclic) :
    Fintype.card V ≤ G.edgeFinset.card := by
  have hle := card_edgeFinset_ge_card_sub_one G hconn
  by_contra hlt
  rw [not_le] at hlt
  have heq : G.edgeFinset.card + 1 = Fintype.card V := by omega
  have htree : G.IsTree := by
    rw [isTree_iff_connected_and_card]
    refine ⟨hconn, ?_⟩
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← edgeFinset_card]
    exact heq
  exact hcyc htree.isAcyclic

theorem conn_cycle_edges_ge_card_int (hconn : G.Connected) (hcyc : ¬ G.IsAcyclic) :
    (Fintype.card V : ℤ) ≤ (G.edgeFinset.card : ℤ) := by
  have := conn_cycle_card_le_edges G hconn hcyc; omega

/-! ### v1.2 §II: product (handshake / edge-count) facts

These relate the *products* n·min_deg, n·max_deg and n² (= n·n) to the edge count.
The deduction engine carries the products as proof-only auxiliary variables
(P_n_mindeg, P_n_maxdeg, N2) and connects them to the original invariants with
McCormick envelope inequalities (the product inference step).  The ℤ wrappers
state the products with the SAME factor order the formalizer renders
(n → Fintype.card V first). -/

-- n · min_deg ≤ 2m  :  ∑_v min_deg ≤ ∑_v deg v = 2m
theorem card_mul_minDegree_le_two_mul_edges :
    Fintype.card V * G.minDegree ≤ 2 * G.edgeFinset.card := by
  have h2 : ∑ _v : V, G.minDegree ≤ ∑ v : V, G.degree v :=
    Finset.sum_le_sum (fun v _ => G.minDegree_le_degree v)
  have h1 : ∑ _v : V, G.minDegree = Fintype.card V * G.minDegree := by
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [h1] at h2
  rwa [G.sum_degrees_eq_twice_card_edges] at h2

-- 2m ≤ n · max_deg  :  2m = ∑_v deg v ≤ ∑_v max_deg
theorem two_mul_edges_le_card_mul_maxDegree :
    2 * G.edgeFinset.card ≤ Fintype.card V * G.maxDegree := by
  have h2 : ∑ v : V, G.degree v ≤ ∑ _v : V, G.maxDegree :=
    Finset.sum_le_sum (fun v _ => G.degree_le_maxDegree v)
  have h1 : ∑ _v : V, G.maxDegree = Fintype.card V * G.maxDegree := by
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [h1, G.sum_degrees_eq_twice_card_edges] at h2
  exact h2

-- product fact 1 : n·min_deg ≤ 2m
theorem handshake_min_int :
    (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≤ 2 * (G.edgeFinset.card : ℤ) := by
  have := card_mul_minDegree_le_two_mul_edges G
  exact_mod_cast this

-- product fact 2 : 2m ≤ n·max_deg
theorem handshake_max_int :
    2 * (G.edgeFinset.card : ℤ) ≤ (Fintype.card V : ℤ) * (G.maxDegree : ℤ) := by
  have := two_mul_edges_le_card_mul_maxDegree G
  exact_mod_cast this

-- regular : 2m = n·d  (ℕ), then 2m = d·n  (ℤ) — linear (d a constant)
theorem regular_two_mul_edges {d : ℕ} (h : G.IsRegularOfDegree d) :
    2 * G.edgeFinset.card = Fintype.card V * d := by
  rw [← G.sum_degrees_eq_twice_card_edges]
  rw [Finset.sum_congr rfl (fun v _ => h v), Finset.sum_const, Finset.card_univ, smul_eq_mul]

theorem regular_edges_int {d : ℕ} (h : G.IsRegularOfDegree d) :
    2 * (G.edgeFinset.card : ℤ) = (d : ℤ) * (Fintype.card V : ℤ) := by
  have h2 := regular_two_mul_edges G h
  rw [mul_comm (d : ℤ) (Fintype.card V : ℤ)]
  exact_mod_cast h2

-- product fact 4 : 2m ≤ n² − n  (via m ≤ n.choose 2 and 2·(n.choose 2) = n·(n−1))
theorem two_mul_edges_le_card_sq_sub_card_int [Nonempty V] :
    2 * (G.edgeFinset.card : ℤ)
      ≤ (Fintype.card V : ℤ) * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) := by
  have h := G.card_edgeFinset_le_card_choose_two
  have hkey : 2 * (Fintype.card V).choose 2 = Fintype.card V * (Fintype.card V - 1) := by
    rw [Nat.choose_two_right, Nat.mul_div_cancel']
    exact (Nat.even_mul_pred_self _).two_dvd
  have h2 : 2 * G.edgeFinset.card ≤ Fintype.card V * (Fintype.card V - 1) := by
    calc 2 * G.edgeFinset.card ≤ 2 * (Fintype.card V).choose 2 := by omega
      _ = Fintype.card V * (Fintype.card V - 1) := hkey
  have hn : 1 ≤ Fintype.card V := Fintype.card_pos
  zify [hn] at h2
  have hexp : (Fintype.card V : ℤ) * ((Fintype.card V : ℤ) - 1)
            = (Fintype.card V : ℤ) * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) := by ring
  linarith [h2, hexp]

-- product fact 5 : is_bipartite ⟹ 4m ≤ n²
theorem bipartite_four_mul_edges_int (h : G.IsBipartite) :
    4 * (G.edgeFinset.card : ℤ) ≤ (Fintype.card V : ℤ) * (Fintype.card V : ℤ) := by
  have hb := h.four_mul_encard_edgeSet_le
  have henc : G.edgeSet.encard = (G.edgeFinset.card : ℕ∞) := by
    rw [Set.encard_eq_coe_toFinset_card]; rfl
  have hcard : ENat.card V = (Fintype.card V : ℕ∞) := by
    rw [ENat.card_eq_coe_fintype_card]
  rw [henc, hcard] at hb
  have hb2 : (4 * G.edgeFinset.card : ℕ) ≤ (Fintype.card V) ^ 2 := by
    have := hb
    rw [← Nat.cast_ofNat (n := 4), ← Nat.cast_mul, ← Nat.cast_pow] at this
    exact_mod_cast this
  have hcast : (4 * G.edgeFinset.card : ℤ) ≤ ((Fintype.card V ^ 2 : ℕ) : ℤ) := by exact_mod_cast hb2
  push_cast at hcast
  nlinarith [hcast]

/-! ### v1.2.1 §VI: second batch of product facts

Turán-type edge bounds (parametric in a clique-number cap r), the n ≤ α·χ product
fact, and ω ≤ Δ + 1.  See domains/graph/inventory.py. -/

-- ω ≤ r  ⟹  CliqueFree (r+1)
theorem cliqueFree_of_cliqueNum_le {r : ℕ} (h : G.cliqueNum ≤ r) : G.CliqueFree (r + 1) := by
  intro s hs
  have hc := hs.isClique.card_le_cliqueNum
  rw [hs.card_eq] at hc
  omega

-- Turán (loose form): ω ≤ r ⟹ 2r·m ≤ (r−1)·n²   (r ≥ 1)
theorem turan_generic {r : ℕ} (hr : 1 ≤ r) (h : (G.cliqueNum : ℤ) ≤ (r : ℤ)) :
    2 * (r : ℤ) * (G.edgeFinset.card : ℤ)
      ≤ ((r : ℤ) - 1) * ((Fintype.card V : ℤ) * (Fintype.card V : ℤ)) := by
  have hr' : G.cliqueNum ≤ r := by exact_mod_cast h
  have hcf := cliqueFree_of_cliqueNum_le G hr'
  have hb := hcf.card_edgeFinset_le
  have ht := SimpleGraph.mul_turanNumber_le (n := Fintype.card V) (r := r)
  have key : 2 * r * G.edgeFinset.card ≤ (r - 1) * Fintype.card V ^ 2 := by
    calc 2 * r * G.edgeFinset.card
        ≤ 2 * r * turanNumber (Fintype.card V) r := by gcongr
      _ ≤ (r - 1) * Fintype.card V ^ 2 := ht
  have hcast : (2 * r * G.edgeFinset.card : ℤ) ≤ (((r - 1) * Fintype.card V ^ 2 : ℕ) : ℤ) := by
    exact_mod_cast key
  rw [Nat.cast_mul, Nat.cast_sub hr, Nat.cast_pow] at hcast
  push_cast at hcast ⊢
  nlinarith [hcast]

-- Turán specialisations r = 2 (Mantel) … 6, each with the concrete constants the
-- formalizer renders (2r·m ≤ (r−1)·n², using the N2 product variable for n²).
theorem turan_r2_int (h : (G.cliqueNum : ℤ) ≤ 2) :
    4 * (G.edgeFinset.card : ℤ) ≤ (Fintype.card V : ℤ) * (Fintype.card V : ℤ) := by
  have := turan_generic G (r := 2) (by norm_num) (by exact_mod_cast h); push_cast at this; linarith
theorem turan_r3_int (h : (G.cliqueNum : ℤ) ≤ 3) :
    6 * (G.edgeFinset.card : ℤ) ≤ 2 * ((Fintype.card V : ℤ) * (Fintype.card V : ℤ)) := by
  have := turan_generic G (r := 3) (by norm_num) (by exact_mod_cast h); push_cast at this; linarith
theorem turan_r4_int (h : (G.cliqueNum : ℤ) ≤ 4) :
    8 * (G.edgeFinset.card : ℤ) ≤ 3 * ((Fintype.card V : ℤ) * (Fintype.card V : ℤ)) := by
  have := turan_generic G (r := 4) (by norm_num) (by exact_mod_cast h); push_cast at this; linarith
theorem turan_r5_int (h : (G.cliqueNum : ℤ) ≤ 5) :
    10 * (G.edgeFinset.card : ℤ) ≤ 4 * ((Fintype.card V : ℤ) * (Fintype.card V : ℤ)) := by
  have := turan_generic G (r := 5) (by norm_num) (by exact_mod_cast h); push_cast at this; linarith
theorem turan_r6_int (h : (G.cliqueNum : ℤ) ≤ 6) :
    12 * (G.edgeFinset.card : ℤ) ≤ 5 * ((Fintype.card V : ℤ) * (Fintype.card V : ℤ)) := by
  have := turan_generic G (r := 6) (by norm_num) (by exact_mod_cast h); push_cast at this; linarith

-- n ≤ α·χ : a χ-colouring partitions V into χ independent sets, each of size ≤ α
theorem card_le_indepNum_mul_chi :
    Fintype.card V ≤ G.indepNum * G.chromaticNumber.toNat := by
  classical
  obtain ⟨C⟩ := G.colorable_chromaticNumber G.colorable_of_fintype
  set k := G.chromaticNumber.toNat
  have hsum : Fintype.card V
      = ∑ c : Fin k, (univ.filter (fun v => C v = c)).card := by
    rw [← Finset.card_univ]
    exact Finset.card_eq_sum_card_fiberwise (fun v _ => Finset.mem_univ (C v))
  have hfib : ∀ c : Fin k, (univ.filter (fun v => C v = c)).card ≤ G.indepNum := by
    intro c
    have hset : (↑(univ.filter (fun v => C v = c)) : Set V) = C.colorClass c := by
      ext v; simp [Coloring.colorClass]
    have hind : G.IsIndepSet (univ.filter (fun v => C v = c) : Finset V) := by
      rw [hset]; exact C.isIndepSet_colorClass c
    exact hind.card_le_indepNum
  calc Fintype.card V = ∑ c : Fin k, (univ.filter (fun v => C v = c)).card := hsum
    _ ≤ ∑ _c : Fin k, G.indepNum := Finset.sum_le_sum (fun c _ => hfib c)
    _ = k * G.indepNum := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    _ = G.indepNum * k := Nat.mul_comm _ _

theorem card_le_alpha_chi_int :
    (Fintype.card V : ℤ) ≤ (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) := by
  have := card_le_indepNum_mul_chi G; exact_mod_cast this

-- ω ≤ Δ + 1 : a vertex of a maximum clique has ≥ ω−1 clique-neighbours
theorem cliqueNum_le_maxDegree_add_one : G.cliqueNum ≤ G.maxDegree + 1 := by
  classical
  obtain ⟨s, hs⟩ := G.exists_isNClique_cliqueNum
  rcases Finset.eq_empty_or_nonempty s with rfl | ⟨v, hv⟩
  · have hc := hs.card_eq; simp at hc; omega
  · have hsub : s.erase v ⊆ G.neighborFinset v := by
      intro w hw
      rw [Finset.mem_erase] at hw
      rw [SimpleGraph.mem_neighborFinset]
      exact hs.isClique (Finset.mem_coe.mpr hv) (Finset.mem_coe.mpr hw.2) (Ne.symm hw.1)
    have h1 : (s.erase v).card ≤ G.degree v := by
      have hle := Finset.card_le_card hsub
      rwa [← SimpleGraph.card_neighborFinset_eq_degree]
    have h2 := G.degree_le_maxDegree v
    have h3 : (s.erase v).card = G.cliqueNum - 1 := by
      rw [Finset.card_erase_of_mem hv, hs.card_eq]
    omega

theorem omega_le_maxdeg_add_one_int : (G.cliqueNum : ℤ) ≤ (G.maxDegree : ℤ) + 1 := by
  have := cliqueNum_le_maxDegree_add_one G; omega

/-! ### v1.2.2 §IV: diameter and cycle bounds -/

-- is_connected ⟹ diam ≤ n − 1  (shortest u–v walk is a path, length < n)
theorem diam_le_card_sub_one (h : G.Connected) : G.diam ≤ Fintype.card V - 1 := by
  have hb : G.ediam ≤ ((Fintype.card V - 1 : ℕ) : ℕ∞) := by
    apply SimpleGraph.ediam_le_of_edist_le
    intro u v
    obtain ⟨w⟩ := h.preconnected u v
    have hlt : (w.toPath : G.Walk u v).length < Fintype.card V := w.toPath.2.length_lt
    have hle : (w.toPath : G.Walk u v).length ≤ Fintype.card V - 1 := by omega
    calc G.edist u v ≤ ((w.toPath : G.Walk u v).length : ℕ∞) := SimpleGraph.edist_le _
      _ ≤ ((Fintype.card V - 1 : ℕ) : ℕ∞) := Nat.cast_le.mpr hle
  have ht := ENat.toNat_le_toNat hb (ENat.natCast_ne_top (Fintype.card V - 1))
  rw [ENat.toNat_coe] at ht
  simpa [SimpleGraph.diam] using ht

theorem diam_le_card_sub_one_int (h : G.Connected) :
    (G.diam : ℤ) ≤ (Fintype.card V : ℤ) - 1 := by
  haveI := h.nonempty
  have h1 : 1 ≤ Fintype.card V := Fintype.card_pos
  have := diam_le_card_sub_one G h; omega

-- has_cycle ⟹ girth ≤ n  (the shortest cycle has distinct vertices)
theorem girth_le_card (h : ¬ G.IsAcyclic) : G.girth ≤ Fintype.card V := by
  obtain ⟨a, w, hw, hwl⟩ := SimpleGraph.exists_egirth_eq_length.mpr h
  have hlen : w.length ≤ Fintype.card V := by
    have hnd : (w.support.tail).Nodup := hw.support_nodup
    have hle := hnd.length_le_card
    simpa [SimpleGraph.Walk.length_support] using hle
  have hle : G.egirth ≤ (Fintype.card V : ℕ∞) := by rw [hwl]; exact_mod_cast hlen
  have ht := ENat.toNat_le_toNat hle (ENat.natCast_ne_top _)
  simpa [SimpleGraph.girth] using ht

theorem girth_le_card_int (h : ¬ G.IsAcyclic) :
    (G.girth : ℤ) ≤ (Fintype.card V : ℤ) := by
  have := girth_le_card G h; omega

-- has_cycle ⟹ m ≥ 3  (a cycle is a trail of length ≥ 3)
theorem three_le_edges (h : ¬ G.IsAcyclic) : 3 ≤ G.edgeFinset.card := by
  obtain ⟨a, w, hw, _⟩ := SimpleGraph.exists_egirth_eq_length.mpr h
  have h3 := hw.isCircuit.three_le_length
  have hle := hw.isCircuit.isTrail.length_le_card_edgeFinset
  omega

theorem three_le_edges_int (h : ¬ G.IsAcyclic) : (3 : ℤ) ≤ (G.edgeFinset.card : ℤ) := by
  have := three_le_edges G h; omega

-- has_cycle ⟹ n ≥ 3  (from 3 ≤ girth ≤ n)
theorem three_le_card_of_cycle (h : ¬ G.IsAcyclic) : 3 ≤ Fintype.card V := by
  have h1 := girth_le_card G h
  have h2 := G.three_le_girth h
  omega

theorem three_le_card_of_cycle_int (h : ¬ G.IsAcyclic) : (3 : ℤ) ≤ (Fintype.card V : ℤ) := by
  have := three_le_card_of_cycle G h; omega

/-! ### v1.2.2 §II: complete graph ⟹ α ≤ 1 (chi ≥ n ⟺ chi = n ⟺ G = ⊤) -/

theorem complete_indep_le_one (hle : Fintype.card V ≤ G.chromaticNumber.toNat) :
    G.indepNum ≤ 1 := by
  have hc := chromaticNumber_toNat_le_card G
  have heqn : G.chromaticNumber.toNat = Fintype.card V := le_antisymm hc hle
  have hne : G.chromaticNumber ≠ ⊤ := chromaticNumber_ne_top G
  have heq : G.chromaticNumber = (Fintype.card V : ℕ∞) := by
    rw [← ENat.natCast_toNat hne, heqn]
  have htop : G = ⊤ := chromaticNumber_eq_card_iff.mp heq
  subst htop
  rw [← SimpleGraph.cliqueNum_compl, compl_top]
  rcases isEmpty_or_nonempty V with he | hne2
  · simp [SimpleGraph.cliqueNum_of_isEmpty]
  · rw [SimpleGraph.cliqueNum_bot]

theorem complete_indep_le_one_int (h : (Fintype.card V : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)) :
    (G.indepNum : ℤ) ≤ 1 := by
  have hn : Fintype.card V ≤ G.chromaticNumber.toNat := by exact_mod_cast h
  have := complete_indep_le_one G hn; omega

/-! ### Cauchy–Schwarz on degrees (B §P1): 4·m² ≤ n · Σ deg²  (new nlinarith action) -/

theorem deg_cauchy_int :
    4 * (G.edgeFinset.card : ℤ) ^ 2
      ≤ (Fintype.card V : ℤ) * ∑ v, ((G.degree v : ℤ)) ^ 2 := by
  have h : (2 * G.edgeFinset.card) ^ 2 ≤ Fintype.card V * ∑ v, (G.degree v) ^ 2 := by
    have hsum := G.sum_degrees_eq_twice_card_edges
    have hcs := sq_sum_le_card_mul_sum_sq (s := (univ : Finset V)) (f := fun v => G.degree v)
    rw [← hsum]; simpa [Finset.card_univ] using hcs
  have hz := (Nat.cast_le (α := ℤ)).2 h
  push_cast at hz ⊢
  nlinarith [hz]

/-! ### property-implication discharge (§II.2, used by the formalizer) -/

theorem isTree_connected (h : G.IsTree) : G.Connected := h.connected
theorem isTree_acyclic (h : G.IsTree) : G.IsAcyclic := h.isAcyclic
theorem isAcyclic_bipartite (h : G.IsAcyclic) : G.IsBipartite :=
  chromaticNumber_le_two_iff_isBipartite.mp h.chromaticNumber_le_two

/-! ### matching number (ν) -/

-- Base instances so Mathlib's canonical `fintypeEdgeSet` synthesizes for `M.coe`.
-- `Fintype (Sym2 M.verts)` is then derived uniquely via `Sym2.instFintype`.
noncomputable instance subgraphVertsFintype (M : G.Subgraph) : Fintype M.verts :=
  Fintype.ofFinite _
noncomputable instance subgraphCoeAdjDecidable (M : G.Subgraph) : DecidableRel M.coe.Adj :=
  Classical.decRel _

/-- The matching number ν(G): the largest number of edges in a matching subgraph. -/
noncomputable def _root_.SimpleGraph.matchingNumber (G : SimpleGraph V) : ℕ :=
  sSup {k | ∃ M : G.Subgraph, M.IsMatching ∧ M.coe.edgeFinset.card = k}

/-- For a matching `M`, the number of matched vertices is `2·(#edges)`.
(Replicates the technique of `SimpleGraph.Subgraph.IsMatching.even_card`.) -/
theorem verts_toFinset_card_eq (M : G.Subgraph) (h : M.IsMatching) [Fintype M.verts] :
    M.verts.toFinset.card = 2 * M.coe.edgeFinset.card := by
  classical
  rw [SimpleGraph.Subgraph.isMatching_iff_forall_degree] at h
  have hsum := SimpleGraph.sum_degrees_eq_twice_card_edges (G := M.coe)
  rw [← hsum]
  rw [Set.toFinset_card]
  rw [Finset.sum_congr rfl (g := fun _ => 1) (by
    intro x _
    have hd : M.degree x.val = 1 := by convert h x.val x.property using 2
    have hc : M.coe.degree x = M.degree x.val := M.coe_degree x
    have : M.coe.degree x = 1 := hc.trans hd
    convert this using 2)]
  rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ]

/-- The core bound: a matching has at most `card V / 2` edges. -/
theorem two_mul_edges_le_card (M : G.Subgraph) (h : M.IsMatching) :
    2 * M.coe.edgeFinset.card ≤ Fintype.card V := by
  classical
  have heq := verts_toFinset_card_eq G M h
  rw [← heq]
  rw [Set.toFinset_card]
  exact Fintype.card_le_of_injective (fun x => x.val) Subtype.val_injective

/-- The edges of a subgraph's coercion inject into the edges of `G`. -/
theorem edges_coe_le_edges (M : G.Subgraph) :
    M.coe.edgeFinset.card ≤ G.edgeFinset.card := by
  classical
  rw [SimpleGraph.edgeFinset_card, SimpleGraph.edgeFinset_card]
  rw [Set.fintypeCard_eq_ncard, Set.fintypeCard_eq_ncard]
  apply Set.ncard_le_ncard_of_injOn (f := Sym2.map (Subtype.val : M.verts → V))
  · intro e he
    have hmem : (Sym2.map (Subtype.val) e) ∈ M.edgeSet := by
      rw [← M.image_coe_edgeSet_coe]
      exact ⟨e, he, rfl⟩
    exact M.edgeSet_subset hmem
  · exact (Sym2.map.injective Subtype.val_injective).injOn

/-- The set of achievable matching sizes. -/
def matchingSet (G : SimpleGraph V) : Set ℕ :=
  {k | ∃ M : G.Subgraph, M.IsMatching ∧ M.coe.edgeFinset.card = k}

theorem matchingSet_nonempty : (matchingSet G).Nonempty := by
  refine ⟨0, (⊥ : G.Subgraph), ?_, ?_⟩
  · intro v hv
    simp only [SimpleGraph.Subgraph.verts_bot, Set.mem_empty_iff_false] at hv
  · rw [Finset.card_eq_zero, SimpleGraph.edgeFinset_eq_empty,
      SimpleGraph.Subgraph.coe_bot]

theorem matchingSet_bddAbove : BddAbove (matchingSet G) := by
  refine ⟨Fintype.card V, ?_⟩
  rintro k ⟨M, hM, rfl⟩
  have := two_mul_edges_le_card G M hM
  omega

theorem matchingNumber_eq_sSup : matchingNumber G = sSup (matchingSet G) := rfl

theorem matchingNumber_mem : matchingNumber G ∈ matchingSet G :=
  Nat.sSup_mem (matchingSet_nonempty G) (matchingSet_bddAbove G)

/-- ν : 2·ν ≤ n. -/
theorem two_mul_matchingNumber_le_card_int :
    2 * (G.matchingNumber : ℤ) ≤ (Fintype.card V : ℤ) := by
  obtain ⟨M, hM, hMcard⟩ := matchingNumber_mem G
  have hle := two_mul_edges_le_card G M hM
  rw [hMcard] at hle
  exact_mod_cast hle

/-- ν ≤ m  (matching number ≤ edges). -/
theorem matchingNumber_le_edges_int :
    (G.matchingNumber : ℤ) ≤ (G.edgeFinset.card : ℤ) := by
  have hle : G.matchingNumber ≤ G.edgeFinset.card := by
    apply csSup_le (matchingSet_nonempty G)
    rintro k ⟨M, hM, rfl⟩
    exact edges_coe_le_edges G M
  exact_mod_cast hle

/-- `#M.coe.edgeFinset = #M.edgeSet` (as `ncard`), via the injective image map. -/
theorem coe_edges_card_eq_edgeSet_ncard (M : G.Subgraph) :
    M.coe.edgeFinset.card = M.edgeSet.ncard := by
  classical
  rw [SimpleGraph.edgeFinset_card, Set.fintypeCard_eq_ncard]
  rw [← M.image_coe_edgeSet_coe]
  rw [Set.ncard_image_of_injective _ (Sym2.map.injective Subtype.val_injective)]

/-- In a matching, the edge containing a given vertex is unique. -/
theorem matching_edge_unique (M : G.Subgraph) (hM : M.IsMatching)
    {v : V} {e1 e2 : Sym2 V} (he1 : e1 ∈ M.edgeSet) (he2 : e2 ∈ M.edgeSet)
    (hv1 : v ∈ e1) (hv2 : v ∈ e2) : e1 = e2 := by
  classical
  obtain ⟨w1, rfl⟩ := Sym2.mem_iff_exists.mp hv1
  obtain ⟨w2, rfl⟩ := Sym2.mem_iff_exists.mp hv2
  have hadj1 : M.Adj v w1 := he1
  have hadj2 : M.Adj v w2 := he2
  have hvmem : v ∈ M.verts := hadj1.fst_mem
  obtain ⟨w, _, hwuniq⟩ := hM hvmem
  have h1 := hwuniq w1 hadj1
  have h2 := hwuniq w2 hadj2
  rw [h1, h2]

/-- For any matching `M` and vertex cover `c`, `#M.edgeSet ≤ #c`
(each matching edge injects to one of its endpoints in the cover). -/
theorem matching_edges_le_cover (M : G.Subgraph) (hM : M.IsMatching)
    {c : Set V} (hc : G.IsVertexCover c) :
    M.edgeSet.ncard ≤ c.ncard := by
  classical
  have hpick : ∀ e ∈ M.edgeSet, ∃ v ∈ c, v ∈ e := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      have hadj : M.Adj a b := he
      have hGadj : G.Adj a b := M.adj_sub hadj
      rcases hc hGadj with ha | hb
      · exact ⟨a, ha, by simp⟩
      · exact ⟨b, hb, by simp [Sym2.mem_iff]⟩
  choose f hfc hfmem using hpick
  apply Set.ncard_le_ncard_of_injOn
    (f := fun e => if h : e ∈ M.edgeSet then f e h else e.out.1)
  · intro e he
    simp only [he, ↓reduceDIte]
    exact hfc e he
  · intro e1 h1 e2 h2 heq
    simp only [h1, h2, ↓reduceDIte] at heq
    have hv1 : f e1 h1 ∈ e1 := hfmem e1 h1
    have hv2 : f e2 h2 ∈ e2 := hfmem e2 h2
    rw [heq] at hv1
    exact matching_edge_unique G M hM h1 h2 hv1 hv2

/-- ν ≤ τ  (matching number ≤ vertex-cover number; weak LP duality). -/
theorem matchingNumber_le_vertexCoverNum_int :
    (G.matchingNumber : ℤ) ≤ (G.vertexCoverNum.toNat : ℤ) := by
  classical
  obtain ⟨c, hc_enc, hc_cover⟩ := G.vertexCoverNum_exists
  have hc_ncard : c.ncard = G.vertexCoverNum.toNat := by rw [Set.ncard, hc_enc]
  have hle : G.matchingNumber ≤ G.vertexCoverNum.toNat := by
    rw [← hc_ncard]
    apply csSup_le (matchingSet_nonempty G)
    rintro k ⟨M, hM, rfl⟩
    rw [coe_edges_card_eq_edgeSet_ncard]
    exact matching_edges_le_cover G M hM hc_cover
  exact_mod_cast hle

/-! ### domination number (γ) — v2.2 §D -/

/-- The domination number γ(G): the smallest size of a dominating finset (every
vertex is in the set or adjacent to it). -/
noncomputable def _root_.SimpleGraph.dominationNumber (G : SimpleGraph V) : ℕ :=
  sInf {k | ∃ s : Finset V, (∀ v, v ∈ s ∨ ∃ w ∈ s, G.Adj v w) ∧ s.card = k}

theorem dominationNumber_univ_mem_set :
    (Fintype.card V) ∈ {k | ∃ s : Finset V, (∀ v, v ∈ s ∨ ∃ w ∈ s, G.Adj v w) ∧ s.card = k} := by
  refine ⟨Finset.univ, ?_, ?_⟩
  · intro v; exact Or.inl (Finset.mem_univ v)
  · simp [Finset.card_univ]

/-- γ ≤ n  (the whole vertex set dominates). -/
theorem dominationNumber_le_card_int :
    (G.dominationNumber : ℤ) ≤ (Fintype.card V : ℤ) := by
  have h : G.dominationNumber ≤ Fintype.card V := Nat.sInf_le (dominationNumber_univ_mem_set G)
  exact_mod_cast h

/-- γ ≥ 1  (a nonempty graph needs at least one dominator). -/
theorem one_le_dominationNumber_int [Nonempty V] :
    (1 : ℤ) ≤ (G.dominationNumber : ℤ) := by
  have hne : {k | ∃ s : Finset V, (∀ v, v ∈ s ∨ ∃ w ∈ s, G.Adj v w) ∧ s.card = k}.Nonempty :=
    ⟨Fintype.card V, dominationNumber_univ_mem_set G⟩
  have h1 : 1 ≤ G.dominationNumber := by
    rw [SimpleGraph.dominationNumber]
    apply le_csInf hne
    intro k hk
    obtain ⟨s, hdom, hcard⟩ := hk
    by_contra hc
    push Not at hc
    interval_cases k
    · have hempty : s = ∅ := Finset.card_eq_zero.mp hcard
      obtain ⟨v⟩ := ‹Nonempty V›
      rcases hdom v with hv | ⟨w, hw, _⟩
      · rw [hempty] at hv; exact absurd hv (Finset.notMem_empty v)
      · rw [hempty] at hw; exact absurd hw (Finset.notMem_empty w)
  exact_mod_cast h1

/-- γ ≤ α  (a maximum independent set is dominating). -/
theorem dominationNumber_le_indepNum_int :
    (G.dominationNumber : ℤ) ≤ (G.indepNum : ℤ) := by
  obtain ⟨s, hs⟩ := G.exists_isNIndepSet_indepNum
  have hindep : G.IsIndepSet s := hs.isIndepSet
  have hcard : s.card = G.indepNum := hs.card_eq
  have hdom : ∀ v, v ∈ s ∨ ∃ w ∈ s, G.Adj v w := by
    intro v
    by_contra hc
    push Not at hc
    obtain ⟨hvs, hvadj⟩ := hc
    have hvindep : G.IsIndepSet (insert v s : Finset V) := by
      rw [SimpleGraph.isIndepSet_iff] at hindep ⊢
      intro x hx y hy hxy
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx hy
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · exact absurd (hx ▸ hy ▸ rfl) hxy
      · subst hx
        intro hadj
        exact hvadj y hy hadj
      · subst hy
        intro hadj
        exact hvadj x hx hadj.symm
      · exact hindep hx hy hxy
    have hvcard : (insert v s).card = G.indepNum + 1 := by
      rw [Finset.card_insert_of_notMem hvs, hcard]
    have hle : (insert v s).card ≤ G.indepNum := hvindep.card_le_indepNum
    omega
  have h : G.dominationNumber ≤ s.card := Nat.sInf_le ⟨s, hdom, rfl⟩
  rw [hcard] at h
  exact_mod_cast h

/-! ### vertex connectivity (κ) — v2.2 §K -/

/-- The vertex connectivity κ(G): the smallest size of a vertex set whose removal
disconnects the graph or leaves ≤ 1 vertex (the latter gives the κ = n−1 convention
for complete graphs). -/
noncomputable def _root_.SimpleGraph.vertexConnectivity (G : SimpleGraph V) : ℕ :=
  sInf {k | ∃ s : Finset V,
    (¬ (G.induce (↑sᶜ : Set V)).Connected ∨ (sᶜ : Finset V).card ≤ 1) ∧ s.card = k}

theorem vertexConnectivity_le_of_cut (s : Finset V)
    (h : ¬ (G.induce (↑sᶜ : Set V)).Connected ∨ (sᶜ : Finset V).card ≤ 1) :
    G.vertexConnectivity ≤ s.card := by
  apply Nat.sInf_le
  exact ⟨s, h, rfl⟩

/-- κ ≤ n − 1. -/
theorem vertexConnectivity_le_card_sub_one_int [Nonempty V] :
    (G.vertexConnectivity : ℤ) ≤ (Fintype.card V : ℤ) - 1 := by
  obtain ⟨v₀⟩ := (inferInstance : Nonempty V)
  set s : Finset V := univ \ {v₀} with hs
  have hcompl : sᶜ = {v₀} := by
    rw [hs]
    ext x
    simp [Finset.mem_compl, Finset.mem_sdiff]
  have hcut : ¬ (G.induce (↑sᶜ : Set V)).Connected ∨ (sᶜ : Finset V).card ≤ 1 := by
    right
    rw [hcompl]
    simp
  have hle := vertexConnectivity_le_of_cut G s hcut
  have hsum : s.card + sᶜ.card = Fintype.card V := Finset.card_add_card_compl s
  have hscard : s.card = Fintype.card V - 1 := by
    rw [hcompl, Finset.card_singleton] at hsum
    omega
  rw [hscard] at hle
  have hpos : 1 ≤ Fintype.card V := Fintype.card_pos
  have : (G.vertexConnectivity : ℤ) ≤ ((Fintype.card V - 1 : ℕ) : ℤ) := by exact_mod_cast hle
  rw [Nat.cast_sub hpos] at this
  push_cast at this ⊢
  linarith

/-- If a vertex `a` has no neighbor in `H` and there is a different vertex `b`, then
`H` is not connected. -/
theorem not_connected_of_isolated {W : Type*} (H : SimpleGraph W)
    (a b : W) (hab : a ≠ b) (hiso : ∀ c, ¬ H.Adj a c) :
    ¬ H.Connected := by
  intro hconn
  have hr : H.Reachable a b := hconn.preconnected a b
  rw [reachable_iff_reflTransGen] at hr
  rcases Relation.ReflTransGen.cases_head hr with h | ⟨c, hac, _⟩
  · exact hab h
  · exact hiso c hac

/-- κ ≤ δ  (Whitney: deleting the neighborhood of a minimum-degree vertex is a cut). -/
theorem vertexConnectivity_le_minDegree_int :
    (G.vertexConnectivity : ℤ) ≤ (G.minDegree : ℤ) := by
  rcases isEmpty_or_nonempty V with hV | hV
  · have h0 : G.vertexConnectivity ≤ 0 := by
      have := vertexConnectivity_le_of_cut G (univ : Finset V) (Or.inr (by simp))
      simpa using this
    have : (G.vertexConnectivity : ℤ) ≤ 0 := by exact_mod_cast h0
    have hmd : (0 : ℤ) ≤ (G.minDegree : ℤ) := by positivity
    linarith
  · obtain ⟨v, hv⟩ := G.exists_minimal_degree_vertex
    set s : Finset V := G.neighborFinset v with hs
    have hv_notmem : v ∉ s := by
      rw [hs, mem_neighborFinset]; exact G.irrefl
    have hv_compl : v ∈ sᶜ := by rw [Finset.mem_compl]; exact hv_notmem
    have hscard : s.card = G.minDegree := by
      rw [hs, card_neighborFinset_eq_degree, ← hv]
    have hcut : ¬ (G.induce (↑sᶜ : Set V)).Connected ∨ (sᶜ : Finset V).card ≤ 1 := by
      by_cases hcard : (sᶜ : Finset V).card ≤ 1
      · exact Or.inr hcard
      · left
        push Not at hcard
        have : ∃ u ∈ sᶜ, u ≠ v := by
          by_contra hcon
          push Not at hcon
          have : (sᶜ : Finset V) ⊆ {v} := by
            intro x hx; simp [hcon x hx]
          have := Finset.card_le_card this
          simp at this
          omega
        obtain ⟨u, hu_mem, hu_ne⟩ := this
        apply not_connected_of_isolated (G.induce (↑sᶜ : Set V))
          (⟨v, by simpa using hv_compl⟩) (⟨u, by simpa using hu_mem⟩)
        · simp only [ne_eq, Subtype.mk.injEq]
          exact fun h => hu_ne h.symm
        · rintro ⟨c, hc⟩
          rw [induce_adj]
          intro hadj
          have hc_in_s : c ∈ s := by rw [hs, mem_neighborFinset]; exact hadj
          have hc_in_compl : c ∈ sᶜ := by simpa using hc
          rw [Finset.mem_compl] at hc_in_compl
          exact hc_in_compl hc_in_s
    have hle := vertexConnectivity_le_of_cut G s hcut
    rw [hscard] at hle
    exact_mod_cast hle

/-- κ ≥ 1  (a connected graph on ≥ 2 vertices cannot be split by removing nothing). -/
theorem one_le_vertexConnectivity_int (h : G.Connected) (hn : 2 ≤ Fintype.card V) :
    (1 : ℤ) ≤ (G.vertexConnectivity : ℤ) := by
  set S : Set ℕ := {k | ∃ s : Finset V,
    (¬ (G.induce (↑sᶜ : Set V)).Connected ∨ (sᶜ : Finset V).card ≤ 1) ∧ s.card = k} with hS
  have hne : S.Nonempty := by
    refine ⟨(univ : Finset V).card, (univ : Finset V), Or.inr ?_, rfl⟩
    simp
  have hge : ∀ k ∈ S, (1 : ℕ) ≤ k := by
    intro k hk
    obtain ⟨s, hcut, hcard⟩ := hk
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      exfalso
      have hsempty : s = ∅ := Finset.card_eq_zero.mp hcard
      subst hsempty
      rw [Finset.compl_empty] at hcut
      rcases hcut with hnc | hcle
      · apply hnc
        have hcoe : (↑(univ : Finset V) : Set V) = Set.univ := by simp
        rw [hcoe]
        exact (SimpleGraph.induceUnivIso G).connected_iff.mpr h
      · rw [Finset.card_univ] at hcle
        omega
    · exact hkpos
  have : (1 : ℕ) ≤ G.vertexConnectivity := by
    rw [SimpleGraph.vertexConnectivity, ← hS]
    exact le_csInf hne hge
  exact_mod_cast this

end PolyForge.Graph
