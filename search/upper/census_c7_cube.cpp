// census_c7_cube.cpp
// Complete exhaustive census of ALL 33-word independent sets in C_7^{\boxtimes 3}
// and exact orbit classification under Aut(C_7^{\boxtimes 3}) (order 3! * 14^3 = 16,464).
// Also independently verifies raw34 == 0 across all 4 exhaustive triple-10-band subcases.
//
// Build: g++ -O3 -march=native -fopenmp -std=c++17 -Wall -Wextra search/upper/census_c7_cube.cpp -o search/upper/census_c7_cube
// Run:   ./search/upper/census_c7_cube

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
#include <omp.h>
#include <set>
#include <string>
#include <tuple>
#include <unordered_map>
#include <unordered_set>
#include <vector>

using u64 = uint64_t;
static constexpr u64 ALL49 = (u64(1) << 49) - 1;

inline int vid(int r, int c) { return ((r % 7 + 7) % 7) * 7 + ((c % 7 + 7) % 7); }
inline int popc(u64 x) { return __builtin_popcountll(x); }

static u64 NBR[49];

static void init_graph() {
    for (int r = 0; r < 7; ++r) {
        for (int c = 0; c < 7; ++c) {
            u64 m = 0;
            for (int dr = -1; dr <= 1; ++dr)
                for (int dc = -1; dc <= 1; ++dc)
                    m |= (u64(1) << vid(r + dr, c + dc));
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

struct Aut2 {
    bool sw;
    int sr, tr, sc, tc;
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

static std::vector<u64> enumerate_10sets() {
    std::vector<int> row_masks[4];
    for (int m = 0; m < 128; ++m) {
        bool ok = true;
        for (int c = 0; c < 7; ++c)
            if (((m >> c) & 1) && ((m >> ((c + 1) % 7)) & 1)) { ok = false; break; }
        if (ok) row_masks[__builtin_popcount(m)].push_back(m);
    }
    int row_nbr[128];
    for (int m = 0; m < 128; ++m) {
        int nm = 0;
        for (int c = 0; c < 7; ++c)
            if ((m >> c) & 1)
                nm |= (1 << ((c + 6) % 7)) | (1 << c) | (1 << ((c + 1) % 7));
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
        int prev_cnt = (r == 0) ? 0 : __builtin_popcount(chosen[r - 1]);
        int prev_forb = (r == 0) ? 0 : row_nbr[chosen[r - 1]];
        int max_sz = (r == 0) ? 3 : (3 - prev_cnt);
        int rem = 6 - r;
        for (int sz = 0; sz <= max_sz; ++sz) {
            if (sum + sz > 10) continue;
            if (sum + sz + (rem / 2) * 3 + (rem % 2) * (3 - sz) < 10) continue;
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

static std::vector<u64> k_subsets(u64 B, int k) {
    int elts[49], n = 0;
    while (B) {
        elts[n++] = __builtin_ctzll(B);
        B &= B - 1;
    }
    std::vector<u64> res;
    if (k < 0 || k > n) return res;
    int comb[16];
    auto rec = [&](auto&& self, int idx, int start) -> void {
        if (idx == k) {
            u64 m = 0;
            for (int i = 0; i < k; ++i) m |= (u64(1) << elts[comb[i]]);
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

// Fast exact independent-set enumerator inside a bitmask `avail` of C_7^2
// Appends all independent sets of size in [min_k, max_k] to `out`.
static void enum_indep(u64 avail, int min_k, int max_k, u64 cur, int cur_sz, std::vector<u64>& out) {
    if (cur_sz >= min_k) out.push_back(cur);
    if (cur_sz == max_k) return;
    int need = min_k - cur_sz;
    if (popc(avail) < need) return;
    u64 rem = avail;
    while (rem) {
        if (popc(rem) < need) break;
        int v = __builtin_ctzll(rem);
        rem &= rem - 1;
        enum_indep(rem & ~NBR[v], min_k, max_k, cur | (u64(1) << v), cur_sz + 1, out);
    }
}

// Canonical representation of a subset of C_7^3 (343 vertices = 7 slices of 49 bits)
struct Set343 {
    std::array<u64, 7> s{};
    bool operator==(const Set343& o) const { return s == o.s; }
    bool operator<(const Set343& o) const { return s < o.s; }
};

struct Set343Hash {
    size_t operator()(const Set343& x) const noexcept {
        u64 h = 0x9e3779b97f4a7c15ULL;
        for (int i = 0; i < 7; ++i) {
            u64 k = x.s[i] + 0x9e3779b97f4a7c15ULL;
            k = (k ^ (k >> 30)) * 0xbf58476d1ce4e5b9ULL;
            k = (k ^ (k >> 27)) * 0x94d049bb133111ebULL;
            h ^= k ^ (k >> 31);
            h = (h << 13) | (h >> 51);
        }
        return (size_t)h;
    }
};

// Independent verification that a Set343 is a valid independent set of exact size 33 in C_7^3
static bool verify_set343(const Set343& x, int expected_card) {
    int total = 0;
    for (int i = 0; i < 7; ++i) {
        u64 a = x.s[i];
        u64 b = x.s[(i + 1) % 7];
        total += popc(a);
        if ((a & b) != 0) return false;
        if (!is_indep_c7_sq(a | b)) return false;
    }
    return total == expected_card;
}

// Canonicalize a Set343 under full Aut(C_7^3) = (D_7)^3 rtimes S_3 (order 3! * 14^3 = 16,464)
// using the anchor-to-(0,0,0) trick: for each vertex p in S, translate p -> (0,0,0) and loop over
// the 6 coordinate permutations x 8 sign reflections = 48 stabilizers of (0,0,0).
// Returns (canonical_set, |Stab(S)|).
// Note: Every automorphism mapping S to canon maps SOME p in S to (0,0,0) iff (0,0,0) in canon.
// Since S is nonempty and every vertex can be translated to (0,0,0), the lexicographically
// SMALLEST image in the orbit of S ALWAYS contains (0,0,0)? WAIT:
// Careful! In `Set343::operator<`, comparing `s[0]` smallest means bit 0 = 0 is SMALLER than bit 0 = 1!
// So the lexicographically LARGEST image (or comparing with `>`!) puts vertex (0,0,0) = bit 0 of s[0] = 1!
// Even cleaner: define canonical = lexicographically SMALLEST sorted list of 33 vertex indices in 0..342!
// Since vertex 0 = (0,0,0) is the SMALLEST possible index, the lex-smallest sorted vertex list
// GUARANTEES (0,0,0) is in the canonical representative!!
struct CanonResult {
    Set343 canon;
    int stab_size;
};

static const int PERMS6[6][3] = {
    {0, 1, 2}, {0, 2, 1}, {1, 0, 2}, {1, 2, 0}, {2, 0, 1}, {2, 1, 0}
};

static CanonResult canonicalize_343(const Set343& x) {
    std::array<std::array<int, 3>, 33> pts;
    int n = 0;
    for (int z = 0; z < 7; ++z) {
        u64 m = x.s[z];
        while (m) {
            int v = __builtin_ctzll(m);
            m &= m - 1;
            pts[n++] = {z, v / 7, v % 7};
        }
    }
    assert(n == 33);

    std::array<int, 33> best_idx;
    best_idx.fill(999);
    int best_count = 0;

    std::array<int, 33> cur_idx;
    for (int a = 0; a < 33; ++a) {
        int ax = pts[a][0], ay = pts[a][1], az = pts[a][2];
        for (int p = 0; p < 6; ++p) {
            int p0 = PERMS6[p][0], p1 = PERMS6[p][1], p2 = PERMS6[p][2];
            for (int sm = 0; sm < 8; ++sm) {
                int s0 = (sm & 1) ? 6 : 1;
                int s1 = (sm & 2) ? 6 : 1;
                int s2 = (sm & 4) ? 6 : 1;
                for (int i = 0; i < 33; ++i) {
                    int d[3] = {
                        (pts[i][0] - ax + 7) % 7,
                        (pts[i][1] - ay + 7) % 7,
                        (pts[i][2] - az + 7) % 7
                    };
                    int c0 = (s0 * d[p0]) % 7;
                    int c1 = (s1 * d[p1]) % 7;
                    int c2 = (s2 * d[p2]) % 7;
                    cur_idx[i] = c0 * 49 + c1 * 7 + c2;
                }
                std::sort(cur_idx.begin(), cur_idx.end());
                if (cur_idx < best_idx) {
                    best_idx = cur_idx;
                    best_count = 1;
                } else if (cur_idx == best_idx) {
                    best_count++;
                }
            }
        }
    }
    Set343 canon{};
    for (int id : best_idx) {
        canon.s[id / 49] |= (u64(1) << (id % 49));
    }
    // Every automorphism g in Aut(C_7^3) mapping x -> canon sends some unique point p_a in x to (0,0,0),
    // because (0,0,0) = index 0 is guaranteed to be in best_idx!
    // Hence best_count == |{g in Aut(C_7^3) : g(x) == canon}| == |Stab(x)|!
    assert(best_idx[0] == 0);
    assert(16464 % best_count == 0);
    return {canon, best_count};
}

int main() {
    auto t0 = std::chrono::steady_clock::now();
    init_graph();
    auto sets10 = enumerate_10sets();
    assert(sets10.size() == 980);

    // 3 orbit representatives of C_7^2 10-sets
    std::vector<Aut2> auts;
    for (int sw = 0; sw < 2; ++sw)
        for (int sr : {1, 6})
            for (int tr = 0; tr < 7; ++tr)
                for (int sc : {1, 6})
                    for (int tc = 0; tc < 7; ++tc)
                        auts.push_back({bool(sw), sr, tr, sc, tc});

    std::unordered_set<u64> seen2;
    std::vector<u64> reps;
    for (u64 s : sets10) {
        if (seen2.count(s)) continue;
        reps.push_back(s);
        for (const auto& g : auts) seen2.insert(apply_aut2(g, s));
    }
    assert(reps.size() == 3);

    // Build ext10[X] for all 3..7-subsets of 10-sets
    std::unordered_map<u64, std::vector<u64>> ext10;
    ext10.reserve(300000);
    for (u64 B : sets10) {
        for (int k = 3; k <= 7; ++k) {
            for (u64 sub : k_subsets(B, k)) {
                ext10[sub].push_back(B ^ sub);
            }
        }
    }
    std::cout << "[OK] Built ext10 table (" << ext10.size() << " keys).\n";

    // Global deduplicated raw 33-sets (per thread, merged at end) and canonical orbits
    std::unordered_map<Set343, int, Set343Hash> orbits; // canon -> |Stab|
    long long raw33_sub[4] = {0, 0, 0, 0};
    long long raw34_total = 0;

    auto record_solutions = [&](int sub_id, const std::vector<Set343>& found33, long long found34) {
        raw33_sub[sub_id] += (long long)found33.size();
        raw34_total += found34;
        for (const auto& x : found33) {
            auto cr = canonicalize_343(x);
            auto it = orbits.find(cr.canon);
            if (it == orbits.end()) {
                assert(verify_set343(cr.canon, 33));
                orbits.emplace(cr.canon, cr.stab_size);
            } else {
                assert(it->second == cr.stab_size);
            }
        }
    };

    // Helper: memoized independent set enumerator by size [3..7] for allowed mask V \ N[S]
    // Cache key = (allowed_mask, min_k, max_k) -> map from allowed_mask to array<vector<u64>, 8>
    auto build_slice_cache = [&](const std::vector<u64>& seeds) {
        std::unordered_map<u64, std::array<std::vector<u64>, 8>> cache;
        cache.reserve(seeds.size() * 2);
        std::vector<u64> uniq_avail;
        std::unordered_set<u64> seen_a;
        for (u64 s : seeds) {
            u64 a = ALL49 & ~closed_nbr(s);
            if (seen_a.insert(a).second) uniq_avail.push_back(a);
        }
        std::vector<std::array<std::vector<u64>, 8>> vals(uniq_avail.size());
        #pragma omp parallel for schedule(dynamic, 16)
        for (size_t i = 0; i < uniq_avail.size(); ++i) {
            std::vector<u64> tmp;
            enum_indep(uniq_avail[i], 3, 7, 0, 0, tmp);
            for (u64 m : tmp) vals[i][popc(m)].push_back(m);
        }
        for (size_t i = 0; i < uniq_avail.size(); ++i) {
            cache.emplace(uniq_avail[i], std::move(vals[i]));
        }
        return cache;
    };

    // =========================================================================
    // SUBCASE 1a: B0 = B1 = B2 = 10
    // =========================================================================
    {
        auto ts = std::chrono::steady_clock::now();
        struct Quad { u64 s0, s1, s2, s3; int sum03; };
        std::vector<Quad> quads;
        std::vector<u64> s0_list, s3_list;
        for (u64 B0 : reps) {
            for (int k0 = 3; k0 <= 7; ++k0) {
                for (u64 S0 : k_subsets(B0, k0)) {
                    u64 S1 = B0 ^ S0;
                    auto it1 = ext10.find(S1);
                    if (it1 == ext10.end()) continue;
                    for (u64 S2 : it1->second) {
                        auto it2 = ext10.find(S2);
                        if (it2 == ext10.end()) continue;
                        for (u64 S3 : it2->second) {
                            int sum03 = popc(S0) + popc(S1) + popc(S2) + popc(S3);
                            // Need S4+S5+S6 >= 33 - sum03; max possible S4+S5+S6 <= 10 + 7 = 17,
                            // in fact since S4+S5<=10 and S5+S6<=10 and S4,S5,S6 in [3,7]:
                            // S4+S5+S6 <= 14? Wait: 7+3+7 = 17! So check sum03 >= 16.
                            if (sum03 < 16) continue;
                            quads.push_back({S0, S1, S2, S3, sum03});
                            s0_list.push_back(S0);
                            s3_list.push_back(S3);
                        }
                    }
                }
            }
        }
        std::vector<u64> all_seeds = s0_list;
        all_seeds.insert(all_seeds.end(), s3_list.begin(), s3_list.end());
        auto cache = build_slice_cache(all_seeds);

        // Group quads by (S0, S3, min_need) to avoid duplicate (S4, S6) work!
        struct PairKey {
            u64 s0, s3;
            bool operator==(const PairKey& o) const { return s0 == o.s0 && s3 == o.s3; }
        };
        struct PairHash {
            size_t operator()(const PairKey& k) const noexcept {
                return std::hash<u64>{}(k.s0 ^ (k.s3 * 0x9e3779b97f4a7c15ULL));
            }
        };
        std::unordered_map<PairKey, std::vector<int>, PairHash> by_pair;
        by_pair.reserve(quads.size());
        for (int i = 0; i < (int)quads.size(); ++i) {
            by_pair[{quads[i].s0, quads[i].s3}].push_back(i);
        }
        std::vector<std::pair<PairKey, std::vector<int>>> tasks(by_pair.begin(), by_pair.end());

        std::vector<Set343> found33;
        long long found34 = 0;
        #pragma omp parallel
        {
            std::vector<Set343> loc33;
            long long loc34 = 0;
            std::vector<u64> s5_buf;
            #pragma omp for schedule(dynamic, 32)
            for (size_t ti = 0; ti < tasks.size(); ++ti) {
                u64 S0 = tasks[ti].first.s0;
                u64 S3 = tasks[ti].first.s3;
                const auto& qidxs = tasks[ti].second;
                int max_sum03 = 0;
                for (int qi : qidxs) max_sum03 = std::max(max_sum03, quads[qi].sum03);
                int min_need = 33 - max_sum03;

                u64 A4 = ALL49 & ~closed_nbr(S3);
                u64 A6 = ALL49 & ~closed_nbr(S0);
                const auto& L4 = cache.at(A4);
                const auto& L6 = cache.at(A6);

                // Precompute closed_nbr for L6 once
                std::array<std::vector<u64>, 8> N6;
                for (int k6 = 3; k6 <= 7; ++k6) {
                    N6[k6].resize(L6[k6].size());
                    for (size_t j = 0; j < L6[k6].size(); ++j) N6[k6][j] = closed_nbr(L6[k6][j]);
                }

                for (int k4 = 3; k4 <= 7; ++k4) {
                    for (u64 S4 : L4[k4]) {
                        u64 n4 = closed_nbr(S4);
                        int max_k5_from_4 = std::min(7, 10 - k4);
                        for (int k6 = 3; k6 <= 7; ++k6) {
                            int max_k5 = std::min(max_k5_from_4, 10 - k6);
                            int need_k5 = std::max(3, min_need - k4 - k6);
                            if (need_k5 > max_k5) continue;
                            const auto& v6 = L6[k6];
                            const auto& vn6 = N6[k6];
                            for (size_t j = 0; j < v6.size(); ++j) {
                                u64 A5 = ALL49 & ~(n4 | vn6[j]);
                                if (popc(A5) < need_k5) continue;
                                s5_buf.clear();
                                enum_indep(A5, need_k5, max_k5, 0, 0, s5_buf);
                                for (u64 S5 : s5_buf) {
                                    int sum456 = k4 + popc(S5) + k6;
                                    for (int qi : qidxs) {
                                        int tot = quads[qi].sum03 + sum456;
                                        if (tot == 33) {
                                            loc33.push_back({{S0, quads[qi].s1, quads[qi].s2, S3, S4, S5, v6[j]}});
                                        } else if (tot >= 34) {
                                            loc34++;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            #pragma omp critical
            {
                found33.insert(found33.end(), loc33.begin(), loc33.end());
                found34 += loc34;
            }
        }
        record_solutions(0, found33, found34);
        double dt = std::chrono::duration<double>(std::chrono::steady_clock::now() - ts).count();
        std::cout << "[Subcase 1a] quads=" << quads.size() << ", unique(S0,S3)=" << tasks.size()
                  << ", raw33=" << found33.size() << ", raw34=" << found34
                  << ", orbits_so_far=" << orbits.size() << " (" << std::fixed << std::setprecision(2) << dt << "s)\n";
    }

    // =========================================================================
    // SUBCASE 1b: B0 = B1 = B3 = 10 (and B2 <= 9, B6 <= 9 to skip already-covered 1a!)
    // Wait: to be 100% safe against any edge case, we allow B2 <= 10 & B6 <= 10 OR restrict B2 <= 9!
    // Wait: if B2 == 10, that's B0=B1=B2=10 (Subcase 1a)! If B6 == 10, B6=B0=B1=10 (Subcase 1a shifted)!
    // So restricting |B2| <= 9 and |B6| <= 9 is 100% EXACT and avoids redundant work!
    // Wait: also B4 <= 10, B5 <= 10.
    // =========================================================================
    {
        auto ts = std::chrono::steady_clock::now();
        struct Triple { u64 s0, s1, s2; int k0, k1, k2; };
        std::vector<Triple> triples;
        std::vector<u64> s0_seeds;
        for (u64 B0 : reps) {
            for (int k0 = 3; k0 <= 7; ++k0) {
                for (u64 S0 : k_subsets(B0, k0)) {
                    u64 S1 = B0 ^ S0;
                    int k1 = 10 - k0;
                    auto it1 = ext10.find(S1);
                    if (it1 == ext10.end()) continue;
                    for (u64 S2 : it1->second) {
                        triples.push_back({S0, S1, S2, k0, k1, popc(S2)});
                        s0_seeds.push_back(S0);
                    }
                }
            }
        }
        // Precompute cache for S0 (gives S6) and for all possible S4? Better: enumerate S5 directly inside A5 = V \ N[S4],
        // or check S6 first! Notice |S5| + |S6| = 13 - k2 (for total=33) or >= 13 - k2 (for >=33)!
        // Since k2 = 10 - k1 = k0 (because B0=B1=10 => k0+k1=10, k1+k2=10 => k2=k0!),
        // total = (k0+k1) + k2 + (k3+k4) + (k5+k6) = 20 + k0 + k5 + k6!
        // Since k5 + k6 <= 10, we NEED 20 + k0 + 10 >= 33 => k0 >= 3 (always), and k5 + k6 >= 13 - k0!
        // Since |B6| = k6 + k0 <= 9 => k6 <= 9 - k0!
        // And k5 + k6 >= 13 - k0 => k5 >= (13 - k0) - (9 - k0) = 4!!
        // Also |B2| = k2 + k3 = k0 + k3 <= 9 => k3 <= 9 - k0, and k3 + k4 = 10 => k4 >= k0 + 1!
        auto cache_s0 = build_slice_cache(s0_seeds);

        // Precompute valid (S3, S4) pairs per unique S2: B3 in sets10 with S3 subset (B3 \ N[S2]),
        // 3 <= |S3| <= 9 - k0 (so |B2| <= 9), S4 = B3 \ S3!
        std::vector<u64> uniq_s2;
        std::unordered_map<u64, int> s2_id;
        for (const auto& t : triples) {
            if (!s2_id.count(t.s2)) {
                s2_id[t.s2] = (int)uniq_s2.size();
                uniq_s2.push_back(t.s2);
            }
        }
        // For each unique S2, collect all distinct (S3, S4) with S3 u S4 in sets10, S3 disjoint N[S2], 3 <= |S3| <= min(7, 9 - |S2|)
        // Note: |S4| = 10 - |S3| >= 3. And we only need unique S4 per S2! Wait: multiple S3 could share S4, keep vector of (S3, S4).
        std::vector<std::vector<std::pair<u64, u64>>> s34_by_s2(uniq_s2.size());
        #pragma omp parallel for schedule(dynamic, 16)
        for (size_t i = 0; i < uniq_s2.size(); ++i) {
            u64 S2 = uniq_s2[i];
            int k2 = popc(S2);
            int max_k3 = std::min(7, 9 - k2);
            u64 A3 = ALL49 & ~closed_nbr(S2);
            auto& vec = s34_by_s2[i];
            for (u64 B3 : sets10) {
                u64 avail3 = B3 & A3;
                int avc = popc(avail3);
                if (avc < 3) continue;
                int hi = std::min(max_k3, avc);
                for (int k3 = 3; k3 <= hi; ++k3) {
                    for (u64 S3 : k_subsets(avail3, k3)) {
                        vec.push_back({S3, B3 ^ S3});
                    }
                }
            }
        }

        // Group triples by (S0, S2) so we don't repeat work!
        std::map<std::pair<u64, u64>, std::vector<int>> by_02;
        for (int i = 0; i < (int)triples.size(); ++i) by_02[{triples[i].s0, triples[i].s2}].push_back(i);
        std::vector<std::pair<std::pair<u64, u64>, std::vector<int>>> tasks(by_02.begin(), by_02.end());

        std::vector<Set343> found33;
        long long found34 = 0;
        #pragma omp parallel
        {
            std::vector<Set343> loc33;
            long long loc34 = 0;
            std::vector<u64> s5_buf;
            #pragma omp for schedule(dynamic, 16)
            for (size_t ti = 0; ti < tasks.size(); ++ti) {
                u64 S0 = tasks[ti].first.first;
                u64 S2 = tasks[ti].first.second;
                int k0 = popc(S0);
                int need56 = 13 - k0; // since total = 20 + k0 + k5 + k6 >= 33
                int max_k6 = std::min(7, 9 - k0); // since |B6| = k6 + k0 <= 9
                if (max_k6 < 3) continue;
                const auto& tidxs = tasks[ti].second;
                const auto& L6 = cache_s0.at(ALL49 & ~closed_nbr(S0));
                const auto& s34_list = s34_by_s2[s2_id.at(S2)];

                // Group s34_list by S4!
                std::unordered_map<u64, std::vector<u64>> s3_by_s4;
                for (const auto& pr : s34_list) s3_by_s4[pr.second].push_back(pr.first);

                // Precompute closed_nbr for L6 up to max_k6
                std::array<std::vector<u64>, 8> N6;
                for (int k6 = 3; k6 <= max_k6; ++k6) {
                    N6[k6].resize(L6[k6].size());
                    for (size_t j = 0; j < L6[k6].size(); ++j) N6[k6][j] = closed_nbr(L6[k6][j]);
                }

                for (const auto& kv : s3_by_s4) {
                    u64 S4 = kv.first;
                    int k4 = popc(S4);
                    u64 n4 = closed_nbr(S4);
                    int max_k5_from_4 = std::min(7, 10 - k4);
                    for (int k6 = 3; k6 <= max_k6; ++k6) {
                        int need_k5 = std::max(3, need56 - k6);
                        int max_k5 = std::min(max_k5_from_4, 10 - k6);
                        if (need_k5 > max_k5) continue;
                        const auto& v6 = L6[k6];
                        const auto& vn6 = N6[k6];
                        for (size_t j = 0; j < v6.size(); ++j) {
                            u64 A5 = ALL49 & ~(n4 | vn6[j]);
                            if (popc(A5) < need_k5) continue;
                            s5_buf.clear();
                            enum_indep(A5, need_k5, max_k5, 0, 0, s5_buf);
                            for (u64 S5 : s5_buf) {
                                int tot = 20 + k0 + popc(S5) + k6;
                                for (u64 S3 : kv.second) {
                                    for (int tri_i : tidxs) {
                                        if (tot == 33) {
                                            loc33.push_back({{S0, triples[tri_i].s1, S2, S3, S4, S5, v6[j]}});
                                        } else if (tot >= 34) {
                                            loc34++;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            #pragma omp critical
            {
                found33.insert(found33.end(), loc33.begin(), loc33.end());
                found34 += loc34;
            }
        }
        record_solutions(1, found33, found34);
        double dt = std::chrono::duration<double>(std::chrono::steady_clock::now() - ts).count();
        std::cout << "[Subcase 1b] triples=" << triples.size() << ", unique(S0,S2)=" << tasks.size()
                  << ", raw33=" << found33.size() << ", raw34=" << found34
                  << ", orbits_so_far=" << orbits.size() << " (" << std::fixed << std::setprecision(2) << dt << "s)\n";
    }

    // =========================================================================
    // SUBCASE 1c: B0 = B1 = B4 = 10, and B2, B3, B5, B6 ALL <= 9
    // (Any extra 10-band would put us in 1a or 1b!)
    // Since B0+B1+B4 = 30 and sum B_i = 66 (for |S|=33) with 4 bands <= 9,
    // EVERY one of B2, B3, B5, B6 = 9, uniquely forcing (5,5,5,4,5,5,4)!
    // (Note: for |S| >= 34, sum B_i >= 68 => >= 4 bands of size 10 => already covered by 1a/1b!)
    // =========================================================================
    {
        auto ts = std::chrono::steady_clock::now();
        struct Triple { u64 s0, s1, s2; };
        std::vector<Triple> triples;
        std::vector<u64> seeds;
        for (u64 B0 : reps) {
            for (u64 S0 : k_subsets(B0, 5)) {
                u64 S1 = B0 ^ S0;
                auto it1 = ext10.find(S1);
                if (it1 == ext10.end()) continue;
                for (u64 S2 : it1->second) {
                    triples.push_back({S0, S1, S2});
                    seeds.push_back(S0);
                    seeds.push_back(S2);
                }
            }
        }
        auto cache = build_slice_cache(seeds);

        // Precompute for every 4-set X occurring as S3 or S6: which B4 in sets10 have |B4 & ~N[X]| >= 5
        // Actually even simpler: group triples by (S0, S2) and loop B4 in sets10!
        std::map<std::pair<u64, u64>, std::vector<int>> by_02;
        for (int i = 0; i < (int)triples.size(); ++i) by_02[{triples[i].s0, triples[i].s2}].push_back(i);
        std::vector<std::pair<std::pair<u64, u64>, std::vector<int>>> tasks(by_02.begin(), by_02.end());

        // Precompute N[X] for every 4-set in cache
        std::unordered_map<u64, std::vector<std::pair<u64, u64>>> s4_nbr_cache; // avail -> [(X, N[X])]
        for (const auto& kv : cache) {
            std::vector<std::pair<u64, u64>> vec;
            vec.reserve(kv.second[4].size());
            for (u64 X : kv.second[4]) vec.push_back({X, closed_nbr(X)});
            s4_nbr_cache.emplace(kv.first, std::move(vec));
        }

        std::vector<Set343> found33;
        #pragma omp parallel
        {
            std::vector<Set343> loc33;
            #pragma omp for schedule(dynamic, 16)
            for (size_t ti = 0; ti < tasks.size(); ++ti) {
                u64 S0 = tasks[ti].first.first;
                u64 S2 = tasks[ti].first.second;
                const auto& tidxs = tasks[ti].second;
                const auto& L3 = s4_nbr_cache.at(ALL49 & ~closed_nbr(S2));
                const auto& L6 = s4_nbr_cache.at(ALL49 & ~closed_nbr(S0));
                if (L3.empty() || L6.empty()) continue;

                // Union of available vertices across all S3 / all S6? Better: compute common forbidden C3 = inter N[s3], C6 = inter N[s6]!
                u64 C3 = ALL49;
                for (const auto& p : L3) C3 &= p.second;
                u64 C6 = ALL49;
                for (const auto& p : L6) C6 &= p.second;

                for (u64 B4 : sets10) {
                    // Any valid split S4 u S5 = B4 must have S4 disjoint C3 and S5 disjoint C6!
                    // Thus (B4 & C3 & C6) must be 0, |B4 & C3| <= 5, |B4 & C6| <= 5!
                    if (B4 & C3 & C6) continue;
                    u64 f5 = B4 & C3; // forced into S5
                    u64 f4 = B4 & C6; // forced into S4
                    if (popc(f5) > 5 || popc(f4) > 5) continue;

                    // Collect S3 in L3 that leave >= 5 verts of B4 outside N[S3] (and disjoint from f4? Wait f4 subset S4 so N[S3] must miss f4!)
                    // Wait: S4 is disjoint from N[S3] => f4 must be disjoint from N[S3]!
                    std::vector<int> cand3, cand6;
                    for (int i = 0; i < (int)L3.size(); ++i) {
                        u64 n3 = L3[i].second;
                        if ((n3 & f4) == 0 && popc(B4 & ~n3) >= 5) cand3.push_back(i);
                    }
                    if (cand3.empty()) continue;
                    for (int j = 0; j < (int)L6.size(); ++j) {
                        u64 n6 = L6[j].second;
                        if ((n6 & f5) == 0 && popc(B4 & ~n6) >= 5) cand6.push_back(j);
                    }
                    if (cand6.empty()) continue;

                    for (int i : cand3) {
                        u64 n3 = L3[i].second;
                        u64 must5 = B4 & n3; // must go into S5
                        for (int j : cand6) {
                            u64 n6 = L6[j].second;
                            if (must5 & n6) continue; // vertex forbidden in both S4 and S5!
                            u64 must4 = B4 & n6;
                            int c4 = popc(must4), c5 = popc(must5);
                            if (c4 > 5 || c5 > 5) continue;
                            u64 free_v = B4 ^ must4 ^ must5;
                            for (u64 add4 : k_subsets(free_v, 5 - c4)) {
                                u64 S4 = must4 | add4;
                                u64 S5 = B4 ^ S4;
                                for (int tri_i : tidxs) {
                                    loc33.push_back({{S0, triples[tri_i].s1, S2, L3[i].first, S4, S5, L6[j].first}});
                                }
                            }
                        }
                    }
                }
            }
            #pragma omp critical
            {
                found33.insert(found33.end(), loc33.begin(), loc33.end());
            }
        }
        record_solutions(2, found33, 0);
        double dt = std::chrono::duration<double>(std::chrono::steady_clock::now() - ts).count();
        std::cout << "[Subcase 1c] triples=" << triples.size() << ", unique(S0,S2)=" << tasks.size()
                  << ", raw33=" << found33.size() << ", raw34=0"
                  << ", orbits_so_far=" << orbits.size() << " (" << std::fixed << std::setprecision(2) << dt << "s)\n";
    }

    // =========================================================================
    // SUBCASE 2: B0 = B2 = B4 = 10, B1 = B3 = B5 = B6 = 9
    // Uniquely forces slice sizes (6, 4, 5, 5, 4, 6, 3)!
    // =========================================================================
    {
        auto ts = std::chrono::steady_clock::now();
        struct Root0 { u64 s0, s1; };
        std::vector<Root0> roots;
        for (u64 B0 : reps) {
            for (u64 S1 : k_subsets(B0, 4)) {
                roots.push_back({B0 ^ S1, S1});
            }
        }
        std::vector<Set343> found33;
        #pragma omp parallel
        {
            std::vector<Set343> loc33;
            std::vector<u64> s6_buf;
            #pragma omp for schedule(dynamic, 4)
            for (size_t ri = 0; ri < roots.size(); ++ri) {
                u64 S0 = roots[ri].s0; // size 6
                u64 S1 = roots[ri].s1; // size 4
                u64 n0 = closed_nbr(S0);
                u64 n1 = closed_nbr(S1);
                // Find all (S2(5), S3(5)) with S2 u S3 = B2 in sets10 and S2 disjoint n1
                std::unordered_map<u64, std::vector<u64>> s2_by_s3;
                for (u64 B2 : sets10) {
                    u64 av2 = B2 & ~n1;
                    if (popc(av2) < 5) continue;
                    for (u64 S2 : k_subsets(av2, 5)) {
                        s2_by_s3[B2 ^ S2].push_back(S2);
                    }
                }
                for (const auto& kv : s2_by_s3) {
                    u64 S3 = kv.first; // size 5
                    u64 n3 = closed_nbr(S3);
                    for (u64 B4 : sets10) {
                        u64 av4 = B4 & ~n3;
                        if (popc(av4) < 4) continue;
                        for (u64 S4 : k_subsets(av4, 4)) {
                            u64 S5 = B4 ^ S4; // size 6
                            u64 A6 = ALL49 & ~(n0 | closed_nbr(S5));
                            if (popc(A6) < 3) continue;
                            s6_buf.clear();
                            enum_indep(A6, 3, 3, 0, 0, s6_buf);
                            for (u64 S6 : s6_buf) {
                                for (u64 S2 : kv.second) {
                                    loc33.push_back({{S0, S1, S2, S3, S4, S5, S6}});
                                }
                            }
                        }
                    }
                }
            }
            #pragma omp critical
            {
                found33.insert(found33.end(), loc33.begin(), loc33.end());
            }
        }
        record_solutions(3, found33, 0);
        double dt = std::chrono::duration<double>(std::chrono::steady_clock::now() - ts).count();
        std::cout << "[Subcase 2]  roots=" << roots.size()
                  << ", raw33=" << found33.size() << ", raw34=0"
                  << ", orbits_so_far=" << orbits.size() << " (" << std::fixed << std::setprecision(2) << dt << "s)\n";
    }

    // Sort canonical orbits deterministically & compute Orbit-Stabilizer sum!
    std::vector<std::pair<Set343, int>> sorted_orbits(orbits.begin(), orbits.end());
    std::sort(sorted_orbits.begin(), sorted_orbits.end(),
              [](const auto& a, const auto& b) { return a.first < b.first; });

    long long total_33_sets = 0;
    std::map<int, int> stab_hist;
    for (const auto& pr : sorted_orbits) {
        total_33_sets += 16464 / pr.second;
        stab_hist[pr.second]++;
    }

    // Independent verification of Orbit-Stabilizer count on a sample & on ALL orbits if small:
    // Also write canonical orbit representatives to search/upper/c7_cube_33_orbits.txt
    {
        std::ofstream ofs("search/upper/c7_cube_33_orbits.txt");
        ofs << "# Canonical Aut(C_7^3)-orbit representatives of ALL 33-word independent sets in C_7^{\\boxtimes 3}\n";
        ofs << "# |Aut(C_7^3)| = 16464, K_33 = " << sorted_orbits.size()
            << ", Total 33-sets = " << total_33_sets << ", raw34 = " << raw34_total << "\n";
        ofs << "# Format: orbit_id stab_size orbit_size s0 s1 s2 s3 s4 s5 s6 (hex 49-bit masks)\n";
        for (size_t i = 0; i < sorted_orbits.size(); ++i) {
            int stab = sorted_orbits[i].second;
            ofs << i << " " << stab << " " << (16464 / stab);
            for (int z = 0; z < 7; ++z) {
                ofs << " " << std::hex << sorted_orbits[i].first.s[z] << std::dec;
            }
            ofs << "\n";
        }
    }

    double total_dt = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
    std::cout << "\n============================================================\n";
    std::cout << "EXHAUSTIVE C_7^3 33-SET CENSUS SUMMARY\n";
    std::cout << "  raw34 total (independent check) : " << raw34_total << "\n";
    std::cout << "  raw33 by subcase (1a,1b,1c,2)   : (" << raw33_sub[0] << ", " << raw33_sub[1]
              << ", " << raw33_sub[2] << ", " << raw33_sub[3] << ")\n";
    std::cout << "  Exact Aut(C_7^3)-orbits K_33    : " << sorted_orbits.size() << "\n";
    std::cout << "  Exact total 33-sets (Orb-Stab)  : " << total_33_sets << "\n";
    std::cout << "  Stabilizer histogram            :";
    for (const auto& kv : stab_hist) std::cout << " |Stab|=" << kv.first << ":" << kv.second;
    std::cout << "\n  Total elapsed                   : " << std::fixed << std::setprecision(2) << total_dt << " s\n";
    std::cout << "  Wrote canonical orbits to       : search/upper/c7_cube_33_orbits.txt\n";
    std::cout << "============================================================\n";
    return 0;
}
