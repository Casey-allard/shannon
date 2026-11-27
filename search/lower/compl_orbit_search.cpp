// Stage 2: Direct d=6 (target >= 71..77) and d=7 (target >= 143+) search
// Compile: g++ -O3 -march=native -std=c++17 search/lower/compl_orbit_search.cpp -o /mnt/nvme2tb/shannon_struct_scratch/compl/compl_orbit_search

#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <numeric>
#include <random>
#include <vector>

static constexpr int N6 = 117649; // 7^6
static constexpr int N7 = 823543; // 7^7

template <int D>
static inline std::array<int, D> decodeD(int id) {
    std::array<int, D> a;
    for (int k = D - 1; k >= 0; --k) { a[k] = id % 7; id /= 7; }
    return a;
}

template <int D>
static inline int encodeD(const std::array<int, D>& a) {
    int id = 0;
    for (int k = 0; k < D; ++k) id = id * 7 + a[k];
    return id;
}

template <int D>
static inline bool is_sepD(const std::array<int, D>& u, const std::array<int, D>& v) {
    for (int k = 0; k < D; ++k) {
        int d = (u[k] - v[k] + 7) % 7;
        if (d == 1 || d == 6) return true;
    }
    return false;
}

template <int D>
static bool verify_indepD(const std::vector<std::array<int, D>>& S) {
    for (size_t i = 0; i < S.size(); ++i) {
        for (size_t j = i + 1; j < S.size(); ++j) {
            if (!is_sepD<D>(S[i], S[j])) return false;
        }
    }
    return true;
}

// Fast exact MIS on up to 512 vertices
struct SmallMIS6 {
    int n;
    std::vector<std::array<uint64_t, 8>> ind_adj;
    int best_sz;
    std::vector<int> best_sol, cur_sol;
    uint64_t nodes = 0, limit = 300000;

    void dfs(const std::array<uint64_t, 8>& cand, int sz) {
        if (nodes > limit) return;
        int rem = 0;
        for (int k = 0; k < 8; ++k) rem += __builtin_popcountll(cand[k]);
        if (sz + rem <= best_sz) return;
        if (rem == 0) {
            if (sz > best_sz) { best_sz = sz; best_sol = cur_sol; }
            return;
        }
        int v = -1;
        for (int k = 0; k < 8; ++k) {
            if (cand[k]) { v = (k << 6) + __builtin_ctzll(cand[k]); break; }
        }
        ++nodes;
        std::array<uint64_t, 8> nxt;
        for (int k = 0; k < 8; ++k) nxt[k] = cand[k] & ind_adj[v][k];
        cur_sol.push_back(v);
        dfs(nxt, sz + 1);
        cur_sol.pop_back();
        std::array<uint64_t, 8> exc = cand;
        exc[v >> 6] &= ~(1ULL << (v & 63));
        dfs(exc, sz);
    }

    template <int D>
    int solve(const std::vector<std::array<int, D>>& verts, int target_min,
              std::vector<std::array<int, D>>& out_sol, uint64_t node_lim = 300000) {
        n = (int)verts.size();
        if (n > 512 || n < target_min) return -1;
        std::vector<std::pair<int, int>> deg(n);
        for (int i = 0; i < n; ++i) {
            int c = 0;
            for (int j = 0; j < n; ++j) if (i != j && is_sepD<D>(verts[i], verts[j])) ++c;
            deg[i] = {c, i};
        }
        std::sort(deg.begin(), deg.end());
        std::vector<std::array<int, D>> sv(n);
        for (int i = 0; i < n; ++i) sv[i] = verts[deg[i].second];
        ind_adj.assign(n, {});
        for (int i = 0; i < n; ++i) {
            ind_adj[i].fill(0ULL);
            for (int j = 0; j < n; ++j) {
                if (i != j && is_sepD<D>(sv[i], sv[j])) ind_adj[i][j >> 6] |= (1ULL << (j & 63));
            }
        }
        std::array<uint64_t, 8> cand{};
        for (int i = 0; i < n; ++i) cand[i >> 6] |= (1ULL << (i & 63));
        best_sz = target_min - 1;
        best_sol.clear();
        cur_sol.clear();
        nodes = 0;
        limit = node_lim;
        dfs(cand, 0);
        out_sol.clear();
        for (int idx : best_sol) out_sol.push_back(sv[idx]);
        return best_sz;
    }
};

// Update tightness array on D=6 or D=7 in O(5^D) time (zero bitset memory!)
template <int D>
static void add_tight(std::vector<int>& tight, const std::array<int, D>& u, int delta) {
    static const int cd[5] = {0, 2, 3, 4, 5};
    if constexpr (D == 6) {
        for (int d0 : cd) { int c0 = (u[0]+d0)%7;
        for (int d1 : cd) { int c1 = (u[1]+d1)%7;
        for (int d2 : cd) { int c2 = (u[2]+d2)%7;
        for (int d3 : cd) { int c3 = (u[3]+d3)%7;
        for (int d4 : cd) { int c4 = (u[4]+d4)%7;
            int base = ((((c0*7+c1)*7+c2)*7+c3)*7+c4)*7;
            for (int d5 : cd) tight[base + (u[5]+d5)%7] += delta;
        }}}}}
    } else if constexpr (D == 7) {
        for (int d0 : cd) { int c0 = (u[0]+d0)%7;
        for (int d1 : cd) { int c1 = (u[1]+d1)%7;
        for (int d2 : cd) { int c2 = (u[2]+d2)%7;
        for (int d3 : cd) { int c3 = (u[3]+d3)%7;
        for (int d4 : cd) { int c4 = (u[4]+d4)%7;
        for (int d5 : cd) { int c5 = (u[5]+d5)%7;
            int base = (((((c0*7+c1)*7+c2)*7+c3)*7+c4)*7+c5)*7;
            for (int d6 : cd) tight[base + (u[6]+d6)%7] += delta;
        }}}}}}
    }
}

// Search order-7 cyclic shift orbits in d=6
static std::vector<std::vector<std::array<int, 6>>> run_d6_orbits(
        int time_sec, int& best6, std::vector<std::array<int, 6>>& best6_sol) {
    auto t0 = std::chrono::steady_clock::now();
    std::vector<std::vector<std::array<int, 6>>> good_sets;
    std::mt19937_64 rng(6006006ULL);

    // Canonical self-independent generators g = (1, 2, 3, a, b, c), 0 <= a <= b <= c <= 3 (by coord negation!)
    // Also test a few extra just in case.
    std::vector<std::array<int, 6>> gens;
    for (int a = 0; a <= 3; ++a)
        for (int b = a; b <= 3; ++b)
            for (int c = b; c <= 3; ++c)
                gens.push_back({1, 2, 3, a, b, c});
    // Also include (1,2,3,1,2,4) explicitly
    gens.push_back({1, 2, 3, 1, 2, 4});

    int max_orbs = 0;
    for (const auto& g : gens) {
        if (std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count() > time_sec) break;
        // Orbits indexed by (0, c1, c2, c3, c4, c5) -> 16807 orbits
        std::vector<std::array<int, 6>> orb0(7);
        for (int t = 0; t < 7; ++t)
            for (int k = 0; k < 6; ++k) orb0[t][k] = (t * g[k]) % 7;

        std::vector<std::array<int, 6>> compat0_bases;
        for (int oid = 1; oid < 16807; ++oid) {
            int tmp = oid;
            std::array<int, 6> base{};
            for (int k = 5; k >= 1; --k) { base[k] = tmp % 7; tmp /= 7; }
            bool ok = true;
            for (int t = 0; t < 7; ++t) {
                std::array<int, 6> w;
                for (int k = 0; k < 6; ++k) w[k] = (base[k] + t * g[k]) % 7;
                if (!is_sepD<6>(w, {0,0,0,0,0,0})) { ok = false; break; }
            }
            if (ok) compat0_bases.push_back(base);
        }
        int M = (int)compat0_bases.size();
        if (M == 0) continue;

        // Build adjacency bitset on compat0_bases (two bases u, v compatible iff forall t in 0..6, sep(u, v + t*g))
        int MW = (M + 63) / 64;
        std::vector<std::vector<uint64_t>> close_orb(M, std::vector<uint64_t>(MW, 0ULL));
        for (int i = 0; i < M; ++i) {
            for (int j = i; j < M; ++j) {
                bool indep = true;
                for (int t = 0; t < 7; ++t) {
                    std::array<int, 6> vt;
                    for (int k = 0; k < 6; ++k) vt[k] = (compat0_bases[j][k] + t * g[k]) % 7;
                    if (!is_sepD<6>(compat0_bases[i], vt)) { indep = false; break; }
                }
                if (!indep) {
                    close_orb[i][j >> 6] |= (1ULL << (j & 63));
                    close_orb[j][i >> 6] |= (1ULL << (i & 63));
                }
            }
        }

        // Fast ILS on M vertices looking for clique >= 9 (10 orbits = 70 words) or 10 (11 orbits = 77 words)!
        int gen_best = 0;
        std::vector<int> tight(M);
        for (int trial = 0; trial < 200; ++trial) {
            std::vector<int> S;
            std::fill(tight.begin(), tight.end(), 0);
            std::vector<int> perm(M);
            std::iota(perm.begin(), perm.end(), 0);
            std::shuffle(perm.begin(), perm.end(), rng);
            for (int v : perm) {
                if (tight[v] == 0) {
                    S.push_back(v);
                    for (int b = 0; b < M; ++b) if ((close_orb[v][b >> 6] >> (b & 63)) & 1ULL) ++tight[b];
                }
            }
            for (int step = 0; step < 300; ++step) {
                // Fill free
                for (int v = 0; v < M; ++v) {
                    if (tight[v] == 0) {
                        S.push_back(v);
                        for (int b = 0; b < M; ++b) if ((close_orb[v][b >> 6] >> (b & 63)) & 1ULL) ++tight[b];
                    }
                }
                if ((int)S.size() > gen_best) {
                    gen_best = (int)S.size();
                }
                if ((int)S.size() >= 9) {
                    std::vector<std::array<int, 6>> sol = orb0;
                    for (int idx : S) {
                        for (int t = 0; t < 7; ++t) {
                            std::array<int, 6> w;
                            for (int k = 0; k < 6; ++k) w[k] = (compat0_bases[idx][k] + t * g[k]) % 7;
                            sol.push_back(w);
                        }
                    }
                    if (verify_indepD<6>(sol)) {
                        if ((int)sol.size() > best6) {
                            best6 = (int)sol.size();
                            best6_sol = sol;
                            std::cout << "[d6-orb] NEW BEST " << best6 << " with g=("
                                      << g[0] << "," << g[1] << "," << g[2] << "," << g[3] << "," << g[4] << "," << g[5] << ")\n";
                        }
                        if (good_sets.size() < 200) good_sets.push_back(std::move(sol));
                    }
                }
                // 1-tight swap
                std::vector<int> c1;
                for (int v = 0; v < M; ++v) if (tight[v] == 1) c1.push_back(v);
                if (!c1.empty()) {
                    int v = c1[rng() % c1.size()];
                    int bi = -1;
                    for (int i = 0; i < (int)S.size(); ++i)
                        if ((close_orb[S[i]][v >> 6] >> (v & 63)) & 1ULL) { bi = i; break; }
                    int rem = S[bi];
                    S[bi] = v;
                    for (int b = 0; b < M; ++b) {
                        int d = ((close_orb[v][b >> 6] >> (b & 63)) & 1ULL) - ((close_orb[rem][b >> 6] >> (b & 63)) & 1ULL);
                        tight[b] += d;
                    }
                } else if (!S.empty()) {
                    int bi = rng() % S.size();
                    int rem = S[bi];
                    S[bi] = S.back(); S.pop_back();
                    for (int b = 0; b < M; ++b) if ((close_orb[rem][b >> 6] >> (b & 63)) & 1ULL) --tight[b];
                }
            }
        }
        if (gen_best + 1 > max_orbs) max_orbs = gen_best + 1;
        std::cout << "[d6-orb] g=(1,2,3," << g[3] << "," << g[4] << "," << g[5] << ") M=" << M
                  << " max_orbits=" << (gen_best + 1) << " (" << (gen_best + 1) * 7 << " words)\n";
    }
    return good_sets;
}

// LNS on d=6 (V6 = 117649) starting from 70-word sets (10-orbit sets + {0,1}xS35)
static void run_d6_lns(std::vector<std::vector<std::array<int, 6>>>& seeds, int time_sec,
                       int& best6, std::vector<std::array<int, 6>>& best6_sol) {
    auto t0 = std::chrono::steady_clock::now();
    std::mt19937_64 rng(616161ULL);
    std::vector<int> tight(N6, 0);
    int trials = 0;

    // First check if ANY seed has free vertices right away!
    for (const auto& s : seeds) {
        std::fill(tight.begin(), tight.end(), 0);
        for (const auto& u : s) add_tight<6>(tight, u, 1);
        std::vector<std::array<int, 6>> fv;
        for (int v = 0; v < N6; ++v) if (tight[v] == 0) fv.push_back(decodeD<6>(v));
        if (!fv.empty()) {
            std::cout << "[d6-lns] Seed already has " << fv.size() << " free vertices!\n";
        }
    }

    // Also run LNS destroying k=4..12 words from seeds
    std::vector<int> ks = {4, 6, 7, 8, 10, 12};
    while (std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count() < time_sec) {
        if (seeds.empty()) break;
        const auto& base = seeds[rng() % seeds.size()];
        int k = ks[rng() % ks.size()];
        if (k >= (int)base.size()) continue;

        std::vector<int> perm(base.size());
        std::iota(perm.begin(), perm.end(), 0);
        std::shuffle(perm.begin(), perm.end(), rng);
        std::vector<bool> drop(base.size(), false);
        for (int i = 0; i < k; ++i) drop[perm[i]] = true;

        std::fill(tight.begin(), tight.end(), 0);
        std::vector<std::array<int, 6>> kept;
        for (size_t i = 0; i < base.size(); ++i) {
            if (!drop[i]) {
                kept.push_back(base[i]);
                add_tight<6>(tight, base[i], 1);
            }
        }
        std::vector<std::array<int, 6>> fv;
        for (int v = 0; v < N6; ++v) if (tight[v] == 0) fv.push_back(decodeD<6>(v));

        if ((int)fv.size() >= k + 1 && (int)fv.size() <= 512) {
            SmallMIS6 mis;
            std::vector<std::array<int, 6>> add_sol;
            int got = mis.solve<6>(fv, best6 - (int)kept.size() + 1, add_sol, 200000);
            if ((int)kept.size() + got > best6) {
                std::vector<std::array<int, 6>> cand = kept;
                cand.insert(cand.end(), add_sol.begin(), add_sol.end());
                if (verify_indepD<6>(cand)) {
                    best6 = (int)cand.size();
                    best6_sol = cand;
                    seeds.push_back(cand);
                    std::cout << "[d6-lns] NEW BEST " << best6 << " (free=" << fv.size() << ", k=" << k << ")!\n";
                }
            }
        }
        ++trials;
    }
    std::cout << "[d6-lns] trials=" << trials << " best6=" << best6 << "\n";
}

// LNS on d=7 (V7 = 823543) starting from {0,1} x best6 (140+ words) -> target >= 143!
static void run_d7_lns(const std::vector<std::array<int, 6>>& base6, int time_sec,
                       int& best7, std::vector<std::array<int, 7>>& best7_sol) {
    auto t0 = std::chrono::steady_clock::now();
    std::mt19937_64 rng(717171ULL);
    std::vector<std::vector<std::array<int, 7>>> seeds7;
    {
        std::vector<std::array<int, 7>> prod;
        for (int x0 : {0, 1}) {
            for (const auto& u : base6) prod.push_back({x0, u[0], u[1], u[2], u[3], u[4], u[5]});
        }
        if (verify_indepD<7>(prod)) {
            best7 = (int)prod.size();
            best7_sol = prod;
            seeds7.push_back(prod);
            std::cout << "[d7-lns] Seed {0,1} x best6 size=" << best7 << "\n";
        }
    }
    std::vector<int> tight(N7, 0);
    std::vector<int> ks = {4, 6, 8, 10};
    int trials = 0;
    while (std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count() < time_sec) {
        if (seeds7.empty()) break;
        const auto& base = seeds7[rng() % seeds7.size()];
        int k = ks[rng() % ks.size()];
        std::vector<int> perm(base.size());
        std::iota(perm.begin(), perm.end(), 0);
        std::shuffle(perm.begin(), perm.end(), rng);
        std::vector<bool> drop(base.size(), false);
        for (int i = 0; i < k; ++i) drop[perm[i]] = true;

        std::fill(tight.begin(), tight.end(), 0);
        std::vector<std::array<int, 7>> kept;
        for (size_t i = 0; i < base.size(); ++i) {
            if (!drop[i]) {
                kept.push_back(base[i]);
                add_tight<7>(tight, base[i], 1);
            }
        }
        std::vector<std::array<int, 7>> fv;
        for (int v = 0; v < N7; ++v) if (tight[v] == 0) fv.push_back(decodeD<7>(v));
        if ((int)fv.size() >= k + 1 && (int)fv.size() <= 512) {
            SmallMIS6 mis;
            std::vector<std::array<int, 7>> add_sol;
            int got = mis.solve<7>(fv, best7 - (int)kept.size() + 1, add_sol, 200000);
            if ((int)kept.size() + got > best7) {
                std::vector<std::array<int, 7>> cand = kept;
                cand.insert(cand.end(), add_sol.begin(), add_sol.end());
                if (verify_indepD<7>(cand)) {
                    best7 = (int)cand.size();
                    best7_sol = cand;
                    seeds7.push_back(cand);
                    std::cout << "[d7-lns] NEW BEST " << best7 << " (free=" << fv.size() << ", k=" << k << ")!\n";
                }
            }
        }
        ++trials;
    }
    std::cout << "[d7-lns] trials=" << trials << " best7=" << best7 << "\n";
}

int main() {
    // Load S35 from Explorer 2 (or d5_best.json if larger)
    std::vector<std::array<int, 5>> s35;
    std::array<int, 5> g5 = {1, 2, 3, 1, 2};
    std::vector<std::array<int, 5>> seeds5 = {{0,0,0,0,0},{0,0,0,1,1},{0,0,1,4,3},{0,2,0,2,1},{0,2,1,1,4}};
    for (const auto& sd : seeds5)
        for (int t = 0; t < 7; ++t)
            s35.push_back({(sd[0]+t*g5[0])%7, (sd[1]+t*g5[1])%7, (sd[2]+t*g5[2])%7, (sd[3]+t*g5[3])%7, (sd[4]+t*g5[4])%7});

    int best6 = 70;
    std::vector<std::array<int, 6>> best6_sol;
    for (int x0 : {0, 1})
        for (const auto& u : s35) best6_sol.push_back({x0, u[0], u[1], u[2], u[3], u[4]});

    auto orb6_seeds = run_d6_orbits(30, best6, best6_sol);
    orb6_seeds.push_back(best6_sol);
    run_d6_lns(orb6_seeds, 25, best6, best6_sol);

    {
        std::ofstream out("/mnt/nvme2tb/shannon_struct_scratch/compl/d6_best.json");
        out << "{\"d\": 6, \"size\": " << best6_sol.size() << ", \"words\": [\n";
        for (size_t i = 0; i < best6_sol.size(); ++i) {
            auto c = best6_sol[i];
            out << "  [" << c[0] << "," << c[1] << "," << c[2] << "," << c[3] << "," << c[4] << "," << c[5] << "]";
            out << (i + 1 < best6_sol.size() ? ",\n" : "\n");
        }
        out << "]}\n";
    }

    int best7 = 0;
    std::vector<std::array<int, 7>> best7_sol;
    run_d7_lns(best6_sol, 20, best7, best7_sol);
    {
        std::ofstream out("/mnt/nvme2tb/shannon_struct_scratch/compl/d7_best.json");
        out << "{\"d\": 7, \"size\": " << best7_sol.size() << ", \"words\": [\n";
        for (size_t i = 0; i < best7_sol.size(); ++i) {
            auto c = best7_sol[i];
            out << "  [" << c[0] << "," << c[1] << "," << c[2] << "," << c[3] << "," << c[4] << "," << c[5] << "," << c[6] << "]";
            out << (i + 1 < best7_sol.size() ? ",\n" : "\n");
        }
        out << "]}\n";
    }
    return 0;
}
