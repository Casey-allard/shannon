// cert_c7_cube.cpp
// Independent C++17 verifier, refuter, and pure-kernel Lean 4 certificate analyzer
// for alpha(C_7^{\boxtimes 3}) = 33.
//
// Build: g++ -O3 -march=native -std=c++17 -Wall -Wextra search/upper/cert_c7_cube.cpp -o search/upper/cert_c7_cube
// Run:   ./search/upper/cert_c7_cube [--emit-lean <path>]

#include <algorithm>
#include <array>
#include <cassert>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <map>
#include <numeric>
#include <set>
#include <string>
#include <tuple>
#include <unordered_map>
#include <unordered_set>
#include <vector>

using u64 = uint64_t;

static constexpr int N2 = 49;
static constexpr u64 ALL49 = (u64(1) << 49) - 1;

inline int vid(int r, int c) { return ((r % 7 + 7) % 7) * 7 + ((c % 7 + 7) % 7); }
inline int vrow(int v) { return v / 7; }
inline int vcol(int v) { return v % 7; }
inline int popc(u64 x) { return __builtin_popcountll(x); }

static u64 NBR[49]; // closed neighborhood in C_7^2

static void init_graph() {
    for (int r = 0; r < 7; ++r) {
        for (int c = 0; c < 7; ++c) {
            u64 m = 0;
            for (int dr = -1; dr <= 1; ++dr) {
                for (int dc = -1; dc <= 1; ++dc) {
                    m |= (u64(1) << vid(r + dr, c + dc));
                }
            }
            NBR[r * 7 + c] = m;
        }
    }
}

inline u64 closed_nbr(u64 s) {
    u64 out = 0;
    while (s) {
        int v = __builtin_ctzll(s);
        s &= s - 1;
        out |= NBR[v];
    }
    return out;
}

inline bool is_indep_c7_sq(u64 s) {
    u64 tmp = s;
    while (tmp) {
        int v = __builtin_ctzll(tmp);
        tmp &= tmp - 1;
        if ((NBR[v] & ~(u64(1) << v)) & s) return false;
    }
    return true;
}

// Apply automorphism (swap, sr, tr, sc, tc) in Aut(C_7^2) (order 2 * 14 * 14 = 392)
// r' = (sr * r + tr) mod 7, c' = (sc * c + tc) mod 7, optional swap(r', c')
struct Aut2 {
    bool sw;
    int sr, tr, sc, tc; // sr, sc in {1, 6}; tr, tc in 0..6
};

inline u64 apply_aut2(const Aut2& g, u64 s) {
    u64 out = 0;
    while (s) {
        int v = __builtin_ctzll(s);
        s &= s - 1;
        int r = v / 7, c = v % 7;
        int r1 = (g.sr * r + g.tr) % 7;
        int c1 = (g.sc * c + g.tc) % 7;
        if (g.sw) std::swap(r1, c1);
        out |= (u64(1) << (r1 * 7 + c1));
    }
    return out;
}

static std::vector<Aut2> all_aut2() {
    std::vector<Aut2> res;
    res.reserve(392);
    for (int sw = 0; sw < 2; ++sw)
        for (int sr : {1, 6})
            for (int tr = 0; tr < 7; ++tr)
                for (int sc : {1, 6})
                    for (int tc = 0; tc < 7; ++tc)
                        res.push_back({bool(sw), sr, tr, sc, tc});
    return res;
}

// Enumerate all 10-sets in C_7^2 by row-by-row backtracking
static std::vector<u64> enumerate_10sets() {
    // Valid nonempty independent row masks (size 1, 2, or 3)
    std::vector<int> row_masks[4];
    for (int m = 0; m < 128; ++m) {
        bool ok = true;
        for (int c = 0; c < 7; ++c) {
            if (((m >> c) & 1) && ((m >> ((c + 1) % 7)) & 1)) {
                ok = false;
                break;
            }
        }
        if (ok) row_masks[__builtin_popcount(m)].push_back(m);
    }
    int row_nbr[128];
    for (int m = 0; m < 128; ++m) {
        int nm = 0;
        for (int c = 0; c < 7; ++c) {
            if ((m >> c) & 1) {
                nm |= (1 << ((c + 6) % 7)) | (1 << c) | (1 << ((c + 1) % 7));
            }
        }
        row_nbr[m] = nm;
    }

    std::vector<u64> sets10;
    int chosen[7];
    auto dfs = [&](auto&& self, int r, int sum) -> void {
        if (r == 7) {
            if (sum == 10 && (row_nbr[chosen[6]] & chosen[0]) == 0) {
                u64 mask = 0;
                for (int i = 0; i < 7; ++i) mask |= (u64(chosen[i]) << (7 * i));
                sets10.push_back(mask);
            }
            return;
        }
        int rem_rows = 7 - r;
        // Max additional from remaining rows: floor(3 * rem_rows / 2) roughly, bound 3*rem_rows
        int prev_cnt = (r == 0) ? 0 : __builtin_popcount(chosen[r - 1]);
        int prev_forb = (r == 0) ? 0 : row_nbr[chosen[r - 1]];
        int max_sz = (r == 0) ? 3 : (3 - prev_cnt);
        for (int sz = 0; sz <= max_sz; ++sz) {
            if (sum + sz > 10) continue;
            // Quick upper bound on remaining rows after r: pairs of rows sum to <= 3
            int rem = rem_rows - 1;
            int max_rem = (rem / 2) * 3 + (rem % 2) * (3 - sz);
            if (sum + sz + max_rem < 10) continue;
            for (int m : row_masks[sz]) {
                if (m & prev_forb) continue;
                chosen[r] = m;
                self(self, r + 1, sum + sz);
            }
        }
    };
    dfs(dfs, 0, 0);
    std::sort(sets10.begin(), sets10.end());
    sets10.erase(std::unique(sets10.begin(), sets10.end()), sets10.end());
    return sets10;
}

static std::string mask_to_coords(u64 m) {
    std::string s = "[";
    bool first = true;
    for (int v = 0; v < 49; ++v) {
        if ((m >> v) & 1) {
            if (!first) s += ", ";
            first = false;
            s += "(" + std::to_string(v / 7) + "," + std::to_string(v % 7) + ")";
        }
    }
    s += "]";
    return s;
}

// Verify the 33-word witness in C_7^3
static void verify_witness_33() {
    static const std::array<std::array<int, 3>, 33> W = {{
        {0,1,1}, {0,4,2}, {0,4,4}, {0,6,0}, {0,6,5},
        {1,1,4}, {1,1,6}, {1,3,0}, {1,6,3},
        {2,1,2}, {2,3,3}, {2,3,5}, {2,5,6}, {2,6,1},
        {3,0,4}, {3,0,6}, {3,2,0}, {3,4,1}, {3,5,4},
        {4,0,2}, {4,2,5}, {4,3,3}, {4,4,6},
        {5,0,5}, {5,1,0}, {5,3,1}, {5,5,2}, {5,5,4}, {5,6,0},
        {6,0,3}, {6,2,3}, {6,2,5}, {6,4,6}
    }};
    for (int i = 0; i < 33; ++i) {
        for (int j = i + 1; j < 33; ++j) {
            bool close = true;
            for (int k = 0; k < 3; ++k) {
                int d = (W[i][k] - W[j][k] + 7) % 7;
                if (d != 0 && d != 1 && d != 6) close = false;
            }
            assert(!close && "Witness 33 has a conflict!");
        }
    }
}

// Generate all k-subsets of a bitmask B
static std::vector<u64> k_subsets(u64 B, int k) {
    std::vector<int> elts;
    for (int v = 0; v < 49; ++v) if ((B >> v) & 1) elts.push_back(v);
    std::vector<u64> res;
    int n = (int)elts.size();
    std::vector<int> comb(k);
    auto rec = [&](auto&& self, int idx, int start) -> void {
        if (idx == k) {
            u64 m = 0;
            for (int x : comb) m |= (u64(1) << elts[x]);
            res.push_back(m);
            return;
        }
        for (int i = start; i <= n - (k - idx); ++i) {
            comb[idx] = i;
            self(self, idx + 1, i + 1);
        }
    };
    rec(rec, 0, 0);
    return res;
}

// Check if alpha(C_7^2[avail]) <= 3; returns true if <= 3, and fills a 3-clique cover if one exists
struct CliqueCover3 {
    bool found = false;
    u64 c[3] = {0, 0, 0};
};

// All 49 2x2 cliques in C_7^2
static u64 SQ22[49];
static void init_cliques() {
    for (int r = 0; r < 7; ++r) {
        for (int c = 0; c < 7; ++c) {
            u64 m = 0;
            m |= (u64(1) << vid(r, c));
            m |= (u64(1) << vid(r, c + 1));
            m |= (u64(1) << vid(r + 1, c));
            m |= (u64(1) << vid(r + 1, c + 1));
            SQ22[r * 7 + c] = m;
        }
    }
}

static bool has_indep_of_size_4(u64 avail) {
    std::vector<int> vs;
    for (int v = 0; v < 49; ++v) if ((avail >> v) & 1) vs.push_back(v);
    int n = (int)vs.size();
    if (n < 4) return false;
    for (int i = 0; i < n; ++i) {
        u64 m1 = avail & ~NBR[vs[i]];
        for (int j = i + 1; j < n; ++j) {
            if (!((m1 >> vs[j]) & 1)) continue;
            u64 m2 = m1 & ~NBR[vs[j]];
            for (int k = j + 1; k < n; ++k) {
                if (!((m2 >> vs[k]) & 1)) continue;
                u64 m3 = m2 & ~NBR[vs[k]];
                for (int l = k + 1; l < n; ++l) {
                    if ((m3 >> vs[l]) & 1) return true;
                }
            }
        }
    }
    return false;
}

// Find a cover of avail by <= 3 cliques (each clique is a 2x2 square or single vertex)
static CliqueCover3 find_3_clique_cover(u64 avail) {
    CliqueCover3 res;
    if (popc(avail) <= 3) {
        res.found = true;
        int idx = 0;
        for (int v = 0; v < 49; ++v) if ((avail >> v) & 1) res.c[idx++] = (u64(1) << v);
        return res;
    }
    // Collect active 2x2 squares that hit avail in >= 2 vertices (plus singletons)
    std::vector<u64> cand;
    for (int i = 0; i < 49; ++i) {
        u64 h = SQ22[i] & avail;
        if (popc(h) >= 2) cand.push_back(SQ22[i]);
    }
    for (int v = 0; v < 49; ++v) {
        if ((avail >> v) & 1) cand.push_back(u64(1) << v);
    }
    // Deduplicate on avail
    int m = (int)cand.size();
    for (int i = 0; i < m; ++i) {
        u64 r1 = avail & ~cand[i];
        if (r1 == 0) { res.found = true; res.c[0] = cand[i]; return res; }
        if (popc(r1) <= 2) {
            res.found = true;
            res.c[0] = cand[i];
            int idx = 1;
            for (int v = 0; v < 49; ++v) if ((r1 >> v) & 1) res.c[idx++] = (u64(1) << v);
            return res;
        }
        for (int j = i; j < m; ++j) {
            u64 r2 = r1 & ~cand[j];
            if (popc(r2) <= 1) {
                res.found = true;
                res.c[0] = cand[i];
                res.c[1] = cand[j];
                res.c[2] = r2;
                return res;
            }
            for (int k = j; k < m; ++k) {
                if ((r2 & ~cand[k]) == 0) {
                    res.found = true;
                    res.c[0] = cand[i];
                    res.c[1] = cand[j];
                    res.c[2] = cand[k];
                    return res;
                }
            }
        }
    }
    return res;
}

int main() {
    auto t0 = std::chrono::steady_clock::now();
    init_graph();
    init_cliques();
    verify_witness_33();
    std::cout << "[OK] 33-word witness in C_7^3 independently verified (0 conflicts).\n";

    auto sets10 = enumerate_10sets();
    assert(sets10.size() == 980);
    std::cout << "[OK] Enumerated all " << sets10.size() << " 10-sets in C_7^2.\n";

    auto auts = all_aut2();
    std::unordered_set<u64> seen;
    std::vector<u64> reps;
    std::vector<int> orb_sizes;
    std::vector<int> stab_sizes;
    for (u64 s : sets10) {
        if (seen.count(s)) continue;
        reps.push_back(s);
        std::unordered_set<u64> orb;
        int stab = 0;
        for (const auto& g : auts) {
            u64 img = apply_aut2(g, s);
            orb.insert(img);
            if (img == s) stab++;
        }
        for (u64 x : orb) seen.insert(x);
        orb_sizes.push_back((int)orb.size());
        stab_sizes.push_back(stab);
    }
    assert(reps.size() == 3);
    for (int o = 0; o < 3; ++o) {
        std::cout << "  Orbit " << o << ": size=" << orb_sizes[o]
                  << ", |Stab|=" << stab_sizes[o]
                  << ", rep=" << mask_to_coords(reps[o]) << "\n";
        // Check if D_7 x D_7 (no swap) hits the whole orbit of rep2
        if (stab_sizes[o] == 2) {
            std::unordered_set<u64> noswap_orb;
            for (const auto& g : auts) {
                if (!g.sw) noswap_orb.insert(apply_aut2(g, reps[o]));
            }
            std::cout << "    (no-swap D_7 x D_7 image size of Orbit " << o << ": " << noswap_orb.size() << ")\n";
            for (const auto& g : auts) {
                if (apply_aut2(g, reps[o]) == reps[o] && (g.sw || g.sr != 1 || g.tr != 0 || g.sc != 1 || g.tc != 0)) {
                    std::cout << "    nontrivial stab element: sw=" << g.sw
                              << " sr=" << g.sr << " tr=" << g.tr
                              << " sc=" << g.sc << " tc=" << g.tc << "\n";
                }
            }
        }
    }

    // Build Ext(X) lookup for all 4-, 5-, 6-subsets of 10-sets
    std::unordered_map<u64, std::vector<u64>> ext4, ext5, ext6;
    for (u64 B : sets10) {
        for (u64 sub : k_subsets(B, 4)) ext4[sub].push_back(B ^ sub);
        for (u64 sub : k_subsets(B, 5)) ext5[sub].push_back(B ^ sub);
        for (u64 sub : k_subsets(B, 6)) ext6[sub].push_back(B ^ sub);
    }
    std::cout << "[OK] Built Ext tables: |dom(ext4)|=" << ext4.size()
              << ", |dom(ext5)|=" << ext5.size()
              << ", |dom(ext6)|=" << ext6.size() << "\n";

    // Precompute closed_nbr intersection for each key in ext4, ext5, ext6
    auto common_nbr_of_ext = [&](const std::unordered_map<u64, std::vector<u64>>& ext, u64 X) -> u64 {
        auto it = ext.find(X);
        if (it == ext.end() || it->second.empty()) return ALL49;
        u64 inter = ALL49;
        for (u64 Y : it->second) inter &= closed_nbr(Y);
        return inter;
    };

    // =========================================================================
    // PROFILE P1+P3: (5,5,5,5,5,5,>=4), center B2 = S2(5) u S3(5)
    // =========================================================================
    {
        int total_halves = 0, root_killed = 0;
        int lvl1_total = 0, lvl1_killed = 0;
        int lvl2_total = 0, lvl2_pop_killed = 0, lvl2_clique_killed = 0, survivors = 0;
        int max_avail_clique = 0;
        for (int o = 0; o < 3; ++o) {
            u64 B2 = reps[o];
            auto subs5 = k_subsets(B2, 5);
            for (u64 S2 : subs5) {
                u64 S3 = B2 ^ S2;
                if (S2 > S3) continue; // palindromic symmetry S2 <-> S3 (reversing coords 0..6)
                total_halves++;
                const auto& L1 = ext5[S2];
                const auto& R4 = ext5[S3];
                u64 CL = ALL49;
                for (u64 s1 : L1) CL &= common_nbr_of_ext(ext5, s1);
                u64 CR = ALL49;
                for (u64 s4 : R4) CR &= common_nbr_of_ext(ext5, s4);
                u64 avail0 = ALL49 & ~(CL | CR);
                if (popc(avail0) <= 3 || !has_indep_of_size_4(avail0)) {
                    root_killed++;
                    continue;
                }
                for (u64 s1 : L1) {
                    u64 c1 = common_nbr_of_ext(ext5, s1);
                    for (u64 s4 : R4) {
                        lvl1_total++;
                        u64 c4 = common_nbr_of_ext(ext5, s4);
                        u64 avail1 = ALL49 & ~(c1 | c4);
                        if (popc(avail1) <= 3 || !has_indep_of_size_4(avail1)) {
                            lvl1_killed++;
                            continue;
                        }
                        for (u64 s0 : ext5[s1]) {
                            u64 n0 = closed_nbr(s0);
                            for (u64 s5 : ext5[s4]) {
                                lvl2_total++;
                                u64 avail2 = ALL49 & ~(n0 | closed_nbr(s5));
                                if (popc(avail2) <= 3) {
                                    lvl2_pop_killed++;
                                } else if (!has_indep_of_size_4(avail2)) {
                                    auto cc = find_3_clique_cover(avail2);
                                    assert(cc.found);
                                    lvl2_clique_killed++;
                                    max_avail_clique = std::max(max_avail_clique, popc(avail2));
                                } else {
                                    survivors++;
                                }
                            }
                        }
                    }
                }
            }
        }
        assert(survivors == 0);
        std::cout << "\n[P1+P3] REFUTED (0 survivors):\n"
                  << "  halves=" << total_halves << ", root_killed=" << root_killed
                  << " (rem=" << (total_halves - root_killed) << ")\n"
                  << "  lvl1_total=" << lvl1_total << ", lvl1_killed=" << lvl1_killed
                  << " (rem=" << (lvl1_total - lvl1_killed) << ")\n"
                  << "  lvl2_total=" << lvl2_total << ", pop<=3=" << lvl2_pop_killed
                  << ", 3-clique=" << lvl2_clique_killed << " (max |avail|=" << max_avail_clique << ")\n";
    }

    // =========================================================================
    // PROFILE P2: (4,6,4,6,4,6,4), center B2 = S2(4) u S3(6)
    // =========================================================================
    {
        int total_cases = 0, root_killed = 0;
        int lvl1_total = 0, lvl1_killed = 0;
        int lvl2_total = 0, lvl2_pop_killed = 0, lvl2_clique_killed = 0, survivors = 0;
        int max_avail_clique = 0;
        for (int o = 0; o < 3; ++o) {
            u64 B2 = reps[o];
            for (u64 S2 : k_subsets(B2, 4)) {
                u64 S3 = B2 ^ S2;
                total_cases++;
                const auto& L1 = ext4[S2]; // |s1| = 6
                const auto& R4 = ext6[S3]; // |s4| = 4
                u64 CL = ALL49;
                for (u64 s1 : L1) CL &= common_nbr_of_ext(ext6, s1); // |s0| = 4
                u64 CR = ALL49;
                for (u64 s4 : R4) CR &= common_nbr_of_ext(ext4, s4); // |s5| = 6
                u64 avail0 = ALL49 & ~(CL | CR);
                if (popc(avail0) <= 3 || !has_indep_of_size_4(avail0)) {
                    root_killed++;
                    continue;
                }
                for (u64 s1 : L1) {
                    u64 c1 = common_nbr_of_ext(ext6, s1);
                    for (u64 s4 : R4) {
                        lvl1_total++;
                        u64 c4 = common_nbr_of_ext(ext4, s4);
                        u64 avail1 = ALL49 & ~(c1 | c4);
                        if (popc(avail1) <= 3 || !has_indep_of_size_4(avail1)) {
                            lvl1_killed++;
                            continue;
                        }
                        for (u64 s0 : ext6[s1]) {
                            u64 n0 = closed_nbr(s0);
                            for (u64 s5 : ext4[s4]) {
                                lvl2_total++;
                                u64 avail2 = ALL49 & ~(n0 | closed_nbr(s5));
                                if (popc(avail2) <= 3) {
                                    lvl2_pop_killed++;
                                } else if (!has_indep_of_size_4(avail2)) {
                                    auto cc = find_3_clique_cover(avail2);
                                    assert(cc.found);
                                    lvl2_clique_killed++;
                                    max_avail_clique = std::max(max_avail_clique, popc(avail2));
                                } else {
                                    survivors++;
                                }
                            }
                        }
                    }
                }
            }
        }
        assert(survivors == 0);
        std::cout << "\n[P2] REFUTED (0 survivors):\n"
                  << "  cases=" << total_cases << ", root_killed=" << root_killed
                  << " (rem=" << (total_cases - root_killed) << ")\n"
                  << "  lvl1_total=" << lvl1_total << ", lvl1_killed=" << lvl1_killed
                  << " (rem=" << (lvl1_total - lvl1_killed) << ")\n"
                  << "  lvl2_total=" << lvl2_total << ", pop<=3=" << lvl2_pop_killed
                  << ", 3-clique=" << lvl2_clique_killed << " (max |avail|=" << max_avail_clique << ")\n";
    }

    // =========================================================================
    // PROFILE P4: (4,6,4,6,4,5,5), center B1 = S1(6) u S2(4)
    // =========================================================================
    {
        int total_cases = 0, root_killed = 0;
        int min_F = 49, max_F = 0;
        int killed_by_row_strip = 0;
        for (int o = 0; o < 3; ++o) {
            u64 B1 = reps[o];
            for (u64 S2 : k_subsets(B1, 4)) {
                u64 S1 = B1 ^ S2;
                total_cases++;
                u64 CL = common_nbr_of_ext(ext6, S1); // forbids S6
                u64 CR = ALL49;
                for (u64 s3 : ext4[S2]) CR &= common_nbr_of_ext(ext6, s3); // forbids S5
                u64 F = CL & CR; // forbids BOTH S5 and S6, hence forbids B5 (a 10-set!)
                min_F = std::min(min_F, popc(F));
                max_F = std::max(max_F, popc(F));
                int hits = 0;
                for (u64 B5 : sets10) {
                    if ((B5 & F) == 0) hits++;
                }
                if (hits == 0) root_killed++;
                // Check if ANY 2x2 square or 1-row/col subset already gives alpha <= 9?
                // Actually check if F contains a whole row (7 verts) or 2x2 or ...
                // Even simpler: check if a 10-clique-free row bound kills it:
                // Any 10-set has row sizes summing to 10 with r_i + r_{i+1} <= 3, so every row has >= 1 vertex!
                // Wait: if F covers an ENTIRE row OR an ENTIRE column, then alpha <= 9 immediately!!
                bool full_rc = false;
                for (int r = 0; r < 7; ++r) {
                    u64 rm = u64(0x7F) << (7 * r);
                    if ((F & rm) == rm) full_rc = true;
                }
                for (int c = 0; c < 7; ++c) {
                    u64 cm = 0;
                    for (int r = 0; r < 7; ++r) cm |= (u64(1) << (7 * r + c));
                    if ((F & cm) == cm) full_rc = true;
                }
                if (full_rc) killed_by_row_strip++;
            }
        }
        assert(root_killed == total_cases);
        std::cout << "\n[P4] REFUTED (0 survivors):\n"
                  << "  cases=" << total_cases << ", root_killed=" << root_killed
                  << ", |F| in [" << min_F << ", " << max_F << "]"
                  << ", full_row_or_col=" << killed_by_row_strip << "\n";
    }

    // =========================================================================
    // PROFILE P5: (5,5,5,5,4,6,4)
    // Test BOTH Strategy A (center B1 = S1(5) u S2(5)) and Strategy B (center B4 = S4(4) u S5(6))
    // =========================================================================
    {
        // Strategy A: center at B1 = S1(5) u S2(5) (378 palindromic halves)
        // Check root (CL, CR) filtering on (B4, S5, S6) and level-1 (s0, s3)!
        // Recall: B4 = S4 u S5 in sets10, S4 disjoint from CR => (B4 & CR) subset S5 (size 6),
        // and B5 = S5 u S6 in sets10, S6 disjoint from CL => S6 in ext6[S5] with (S6 & CL) == 0.
        auto can_complete_3slice = [&](u64 CL, u64 CR, int& cand_B4_out, int& cand_S5_out) -> bool {
            cand_B4_out = 0;
            cand_S5_out = 0;
            for (u64 B4 : sets10) {
                u64 forced5 = B4 & CR;
                int k = popc(forced5);
                if (k > 6) continue;
                cand_B4_out++;
                u64 opt = B4 ^ forced5;
                for (u64 add : k_subsets(opt, 6 - k)) {
                    u64 S5 = forced5 | add;
                    cand_S5_out++;
                    for (u64 S6 : ext6[S5]) {
                        if ((S6 & CL) == 0) return true;
                    }
                }
            }
            return false;
        };

        int halves = 0, root_killed = 0;
        int lvl1_pairs = 0, lvl1_killed = 0, survivors = 0;
        long long sum_cand_B4_root = 0, sum_cand_S5_root = 0;
        long long sum_cand_B4_l1 = 0, sum_cand_S5_l1 = 0;
        int root_min_CR = 49, root_min_CL = 49;
        // Also check: at root, what if we check B4/B5 by just B4 & CR and B5 & CL?
        // Actually even simpler: pre-filter sets10 by |B & CR| <= 6!
        for (int o = 0; o < 3; ++o) {
            u64 B1 = reps[o];
            for (u64 S1 : k_subsets(B1, 5)) {
                u64 S2 = B1 ^ S1;
                if (S1 > S2) continue;
                halves++;
                u64 CL = common_nbr_of_ext(ext5, S1);
                u64 CR = common_nbr_of_ext(ext5, S2);
                root_min_CL = std::min(root_min_CL, popc(CL));
                root_min_CR = std::min(root_min_CR, popc(CR));
                int cB4 = 0, cS5 = 0;
                if (!can_complete_3slice(CL, CR, cB4, cS5)) {
                    root_killed++;
                    sum_cand_B4_root += cB4;
                    sum_cand_S5_root += cS5;
                    continue;
                }
                // Try splitting ONLY on S0 (holding CR fixed) first!
                // Wait: let's measure 1-side split vs 2-side split!
                for (u64 s0 : ext5[S1]) {
                    u64 n0 = closed_nbr(s0);
                    for (u64 s3 : ext5[S2]) {
                        lvl1_pairs++;
                        int cb = 0, cs = 0;
                        if (!can_complete_3slice(n0, closed_nbr(s3), cb, cs)) {
                            lvl1_killed++;
                            sum_cand_B4_l1 += cb;
                            sum_cand_S5_l1 += cs;
                        } else {
                            survivors++;
                        }
                    }
                }
            }
        }
        assert(survivors == 0);
        std::cout << "\n[P5 Strategy A (center B1, 3-slice exact)] REFUTED (0 survivors):\n"
                  << "  halves=" << halves << ", root_killed=" << root_killed
                  << " (rem=" << (halves - root_killed) << "), min|CL|=" << root_min_CL
                  << ", min|CR|=" << root_min_CR << "\n"
                  << "  root_killed avg cand_B4=" << (root_killed ? double(sum_cand_B4_root)/root_killed : 0)
                  << ", avg cand_S5=" << (root_killed ? double(sum_cand_S5_root)/root_killed : 0) << "\n"
                  << "  lvl1_pairs=" << lvl1_pairs << ", lvl1_killed=" << lvl1_killed
                  << ", lvl1 avg cand_B4=" << (lvl1_killed ? double(sum_cand_B4_l1)/lvl1_killed : 0)
                  << ", avg cand_S5=" << (lvl1_killed ? double(sum_cand_S5_l1)/lvl1_killed : 0) << "\n";
    }

    // Also test P5 Strategy A with 1-side split (split s0 OR s3 first before (s0, s3))!
    {
        auto can_complete_3slice = [&](u64 CL, u64 CR) -> bool {
            for (u64 B4 : sets10) {
                u64 forced5 = B4 & CR;
                int k = popc(forced5);
                if (k > 6) continue;
                u64 opt = B4 ^ forced5;
                for (u64 add : k_subsets(opt, 6 - k)) {
                    u64 S5 = forced5 | add;
                    for (u64 S6 : ext6[S5]) {
                        if ((S6 & CL) == 0) return true;
                    }
                }
            }
            return false;
        };
        int halves = 0, root_killed = 0, one_side_killed = 0, s0_nodes = 0, pair_nodes = 0;
        for (int o = 0; o < 3; ++o) {
            u64 B1 = reps[o];
            for (u64 S1 : k_subsets(B1, 5)) {
                u64 S2 = B1 ^ S1;
                if (S1 > S2) continue;
                halves++;
                u64 CL = common_nbr_of_ext(ext5, S1);
                u64 CR = common_nbr_of_ext(ext5, S2);
                if (!can_complete_3slice(CL, CR)) { root_killed++; continue; }
                bool all_s0_ok = true;
                for (u64 s0 : ext5[S1]) {
                    s0_nodes++;
                    if (!can_complete_3slice(closed_nbr(s0), CR)) continue;
                    all_s0_ok = false;
                    for (u64 s3 : ext5[S2]) {
                        pair_nodes++;
                        assert(!can_complete_3slice(closed_nbr(s0), closed_nbr(s3)));
                    }
                }
                if (all_s0_ok) one_side_killed++;
            }
        }
        std::cout << "[P5 Strategy A (with 1-side s0 split)]: root_killed=" << root_killed
                  << ", all_s0_killed=" << one_side_killed
                  << ", s0_nodes=" << s0_nodes << ", pair_nodes=" << pair_nodes << "\n";
    }

    // Also test P5 Strategy B: center at B4 = S4(4) u S5(6) (630 cases)!
    // S6 in ext6[S5] (only 2,871 pairs total!).
    // Need 4-slice chain (S0, S1, S2, S3) of sizes (5,5,5,5) with B0,B1,B2 in sets10,
    // S3 disjoint from N[S4], S0 disjoint from N[S6].
    // Equivalently: B2 = S2 u S3 with S3 subset V \ N[S4] (so B2 & N[S4] subset S2, |B2 & N[S4]| <= 5),
    // and B0 = S0 u S1 with S0 subset V \ N[S6] (so B0 & N[S6] subset S1, |B0 & N[S6]| <= 5),
    // and S1 u S2 = B1 in sets10!
    {
        int total_cases = 0, total_s6 = 0;
        int root_empty_B2 = 0, root_killed = 0, s6_killed = 0;
        long long sum_S2_root = 0, sum_S1_from_S2 = 0;
        for (int o = 0; o < 3; ++o) {
            u64 B4 = reps[o];
            for (u64 S4 : k_subsets(B4, 4)) {
                u64 S5 = B4 ^ S4;
                total_cases++;
                u64 N4 = closed_nbr(S4);
                // Find all valid S2 (size 5) such that some S3 in ext5[S2] is disjoint from N4
                std::vector<u64> valid_S2;
                for (u64 B2 : sets10) {
                    u64 f2 = B2 & N4;
                    int k = popc(f2);
                    if (k > 5) continue;
                    for (u64 add : k_subsets(B2 ^ f2, 5 - k)) valid_S2.push_back(f2 | add);
                }
                std::sort(valid_S2.begin(), valid_S2.end());
                valid_S2.erase(std::unique(valid_S2.begin(), valid_S2.end()), valid_S2.end());
                sum_S2_root += (long long)valid_S2.size();
                if (valid_S2.empty()) { root_empty_B2++; root_killed++; continue; }

                // Find all valid S1 in union_{S2 in valid_S2} ext5[S2]
                std::vector<u64> valid_S1;
                for (u64 S2 : valid_S2) {
                    for (u64 S1 : ext5[S2]) valid_S1.push_back(S1);
                }
                std::sort(valid_S1.begin(), valid_S1.end());
                valid_S1.erase(std::unique(valid_S1.begin(), valid_S1.end()), valid_S1.end());
                sum_S1_from_S2 += (long long)valid_S1.size();

                // Check against C6 = common_nbr_of_ext(ext6, S5)
                u64 C6 = common_nbr_of_ext(ext6, S5);
                bool survives_root = false;
                for (u64 S1 : valid_S1) {
                    for (u64 S0 : ext5[S1]) {
                        if ((S0 & C6) == 0) { survives_root = true; break; }
                    }
                    if (survives_root) break;
                }
                if (!survives_root) { root_killed++; continue; }
                for (u64 S6 : ext6[S5]) {
                    total_s6++;
                    u64 N6 = closed_nbr(S6);
                    bool survives_s6 = false;
                    for (u64 S1 : valid_S1) {
                        for (u64 S0 : ext5[S1]) {
                            if ((S0 & N6) == 0) { survives_s6 = true; break; }
                        }
                        if (survives_s6) break;
                    }
                    assert(!survives_s6);
                    s6_killed++;
                }
            }
        }
        std::cout << "\n[P5 Strategy B (center B4 = S4(4) u S5(6))] REFUTED (0 survivors):\n"
                  << "  cases=" << total_cases << ", root_empty_B2=" << root_empty_B2
                  << ", root_killed=" << root_killed << " (rem=" << (total_cases - root_killed) << ")\n"
                  << "  s6_checked=" << total_s6 << ", s6_killed=" << s6_killed << "\n"
                  << "  avg |valid_S2|=" << double(sum_S2_root)/total_cases
                  << ", avg |valid_S1|=" << double(sum_S1_from_S2)/total_cases << "\n";
    }

    auto t1 = std::chrono::steady_clock::now();
    double dt = std::chrono::duration<double>(t1 - t0).count();
    std::cout << "\nTotal elapsed: " << std::fixed << std::setprecision(3) << dt << " s\n";
    return 0;
}
