// Stage 1: Deep search for alpha((C7^c)^⊠5) >= 36..39
// Compile: g++ -O3 -march=native -std=c++17 search/lower/compl_d5_search.cpp -o /mnt/nvme2tb/shannon_struct_scratch/compl/compl_d5_search

#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <numeric>
#include <random>
#include <vector>

static constexpr int N5 = 16807;
static constexpr int W5 = (N5 + 63) / 64; // 263

struct Bitset5 {
    uint64_t w[W5];
    void clear() { std::fill(w, w + W5, 0ULL); }
    void set_all_valid() {
        std::fill(w, w + W5, ~0ULL);
        int rem = N5 % 64;
        if (rem) w[W5 - 1] = (1ULL << rem) - 1ULL;
    }
    inline void set(int i) { w[i >> 6] |= (1ULL << (i & 63)); }
    inline void reset(int i) { w[i >> 6] &= ~(1ULL << (i & 63)); }
    inline bool test(int i) const { return (w[i >> 6] >> (i & 63)) & 1ULL; }
    inline int popcount() const {
        int s = 0;
        for (int i = 0; i < W5; ++i) s += __builtin_popcountll(w[i]);
        return s;
    }
};

static std::array<int, 5> decode5(int id) {
    std::array<int, 5> a;
    for (int k = 4; k >= 0; --k) { a[k] = id % 7; id /= 7; }
    return a;
}

static int encode5(const std::array<int, 5>& a) {
    int id = 0;
    for (int k = 0; k < 5; ++k) id = id * 7 + a[k];
    return id;
}

static inline bool is_sep5(const std::array<int, 5>& u, const std::array<int, 5>& v) {
    for (int k = 0; k < 5; ++k) {
        int d = (u[k] - v[k] + 7) % 7;
        if (d == 1 || d == 6) return true;
    }
    return false;
}

// Global conflict bitsets (close_mask[u] has bit v iff NOT sep(u, v))
static std::vector<Bitset5> close_mask;
static std::array<std::array<int, 5>, N5> coords5;

static void init_graph5() {
    close_mask.resize(N5);
    for (int i = 0; i < N5; ++i) coords5[i] = decode5(i);
    static const int cd[5] = {0, 2, 3, 4, 5};
    for (int u = 0; u < N5; ++u) {
        close_mask[u].clear();
        const auto& a = coords5[u];
        for (int d0 : cd) {
            int c0 = (a[0] + d0) % 7;
            for (int d1 : cd) {
                int c1 = (a[1] + d1) % 7;
                for (int d2 : cd) {
                    int c2 = (a[2] + d2) % 7;
                    for (int d3 : cd) {
                        int c3 = (a[3] + d3) % 7;
                        int base = (((c0 * 7 + c1) * 7 + c2) * 7 + c3) * 7;
                        for (int d4 : cd) {
                            close_mask[u].set(base + (a[4] + d4) % 7);
                        }
                    }
                }
            }
        }
    }
}

// Exact branch-and-bound MIS on a small induced subgraph of V5
struct SmallMIS {
    int n;
    std::vector<int> orig_ids;
    std::vector<std::array<uint64_t, 8>> ind_adj; // up to 512 vertices (independent neighbors = NOT close)
    int best_sz;
    std::vector<int> best_sol, cur_sol;
    uint64_t nodes = 0;
    uint64_t node_limit = 2000000;

    void dfs(const std::array<uint64_t, 8>& cand, int sz) {
        if (nodes > node_limit) return;
        int rem = 0;
        for (int k = 0; k < 8; ++k) rem += __builtin_popcountll(cand[k]);
        if (sz + rem <= best_sz) return;
        if (rem == 0) {
            if (sz > best_sz) {
                best_sz = sz;
                best_sol = cur_sol;
            }
            return;
        }
        // Pick lowest-degree or first vertex; actually greedy coloring upper bound is even tighter,
        // or pick vertex with fewest remaining compatible neighbors to branch tightly!
        // Simple fast branch: pick first set bit v (ordered by degree ascending).
        int v = -1;
        for (int k = 0; k < 8; ++k) {
            if (cand[k]) {
                v = (k << 6) + __builtin_ctzll(cand[k]);
                break;
            }
        }
        ++nodes;
        // Branch 1: include v
        std::array<uint64_t, 8> nxt;
        for (int k = 0; k < 8; ++k) nxt[k] = cand[k] & ind_adj[v][k];
        cur_sol.push_back(v);
        dfs(nxt, sz + 1);
        cur_sol.pop_back();

        // Branch 2: exclude v
        std::array<uint64_t, 8> exc = cand;
        exc[v >> 6] &= ~(1ULL << (v & 63));
        dfs(exc, sz);
    }

    int solve(const std::vector<int>& verts, int target_min, uint64_t limit = 500000) {
        n = (int)verts.size();
        if (n > 512 || n < target_min) return -1;
        orig_ids = verts;
        // Order by ascending compatible-degree (or descending conflict degree)
        std::vector<std::pair<int, int>> deg(n);
        for (int i = 0; i < n; ++i) {
            int c = 0;
            for (int j = 0; j < n; ++j) {
                if (i != j && !close_mask[verts[i]].test(verts[j])) ++c;
            }
            deg[i] = {c, i};
        }
        std::sort(deg.begin(), deg.end());
        std::vector<int> sorted_verts(n);
        for (int i = 0; i < n; ++i) sorted_verts[i] = verts[deg[i].second];
        orig_ids = sorted_verts;

        ind_adj.assign(n, {});
        for (int i = 0; i < n; ++i) {
            ind_adj[i].fill(0ULL);
            for (int j = 0; j < n; ++j) {
                if (i != j && !close_mask[orig_ids[i]].test(orig_ids[j])) {
                    ind_adj[i][j >> 6] |= (1ULL << (j & 63));
                }
            }
        }
        std::array<uint64_t, 8> cand{};
        for (int i = 0; i < n; ++i) cand[i >> 6] |= (1ULL << (i & 63));
        best_sz = target_min - 1;
        best_sol.clear();
        cur_sol.clear();
        nodes = 0;
        node_limit = limit;
        dfs(cand, 0);
        return best_sz;
    }
};

static bool verify_indep5(const std::vector<int>& S) {
    for (size_t i = 0; i < S.size(); ++i) {
        for (size_t j = i + 1; j < S.size(); ++j) {
            if (close_mask[S[i]].test(S[j])) return false;
        }
    }
    return true;
}

static void print_sol(const char* tag, const std::vector<int>& S) {
    std::cout << "[" << tag << "] FOUND SIZE " << S.size() << ": [";
    for (size_t i = 0; i < S.size(); ++i) {
        auto c = coords5[S[i]];
        std::cout << "(" << c[0] << "," << c[1] << "," << c[2] << "," << c[3] << "," << c[4] << ")";
        if (i + 1 < S.size()) std::cout << ",";
    }
    std::cout << "]" << std::endl;
}

// Subtask 1A: Enumerate all 5-orbit and 4-orbit codes for all canonical generators (1,2,3,a,b)
static std::vector<std::vector<int>> run_orbit_search(int& global_best, std::vector<int>& global_best_sol) {
    std::vector<std::vector<int>> orbit5_codes;
    int total_5orb = 0, total_4orb = 0;
    int max_4orb_free = 0;

    for (int a = 0; a <= 6; ++a) {
        for (int b = a; b <= 6; ++b) {
            std::array<int, 5> g = {1, 2, 3, a, b};
            // Check self-independence of g: g, 2g, 3g must all be separated from 0
            bool ok = true;
            for (int t = 1; t <= 3; ++t) {
                std::array<int, 5> tg;
                for (int k = 0; k < 5; ++k) tg[k] = (t * g[k]) % 7;
                if (!is_sep5(tg, {0,0,0,0,0})) { ok = false; break; }
            }
            if (!ok) continue;

            // 2401 orbits indexed by (0, c1, c2, c3, c4)
            std::array<std::vector<int>, 2401> orb_verts;
            std::vector<Bitset5> orb_close(2401);
            for (int oid = 0; oid < 2401; ++oid) {
                int tmp = oid;
                std::array<int, 5> base{};
                for (int k = 4; k >= 1; --k) { base[k] = tmp % 7; tmp /= 7; }
                orb_close[oid].clear();
                for (int t = 0; t < 7; ++t) {
                    std::array<int, 5> w;
                    for (int k = 0; k < 5; ++k) w[k] = (base[k] + t * g[k]) % 7;
                    int vid = encode5(w);
                    orb_verts[oid].push_back(vid);
                    for (int k = 0; k < W5; ++k) orb_close[oid].w[k] |= close_mask[vid].w[k];
                }
            }

            // Orbits compatible with orbit 0
            std::vector<int> compat0;
            for (int oid = 1; oid < 2401; ++oid) {
                bool indep = true;
                for (int v : orb_verts[oid]) {
                    if (orb_close[0].test(v)) { indep = false; break; }
                }
                if (indep) compat0.push_back(oid);
            }
            if (compat0.empty()) continue;

            int m = (int)compat0.size();
            // Build bitset adjacency on compat0 (m <= 400 -> 7 uint64_ts)
            std::vector<std::array<uint64_t, 8>> adj(m);
            for (int i = 0; i < m; ++i) {
                adj[i].fill(0ULL);
                int oi = compat0[i];
                for (int j = i + 1; j < m; ++j) {
                    int oj = compat0[j];
                    bool indep = true;
                    for (int v : orb_verts[oj]) {
                        if (orb_close[oi].test(v)) { indep = false; break; }
                    }
                    if (indep) adj[i][j >> 6] |= (1ULL << (j & 63));
                }
            }

            // Enumerate 3-cliques and 4-cliques in compat0 (= 4-orbit and 5-orbit codes)
            int gen_4orb = 0, gen_5orb = 0;
            for (int i = 0; i < m; ++i) {
                for (int j = i + 1; j < m; ++j) {
                    if (!((adj[i][j >> 6] >> (j & 63)) & 1ULL)) continue;
                    // Common neighbors > j
                    std::array<uint64_t, 8> c3;
                    for (int w = 0; w < 8; ++w) c3[w] = adj[i][w] & adj[j][w];
                    for (int w = 0; w < 8; ++w) {
                        uint64_t bits = c3[w];
                        while (bits) {
                            int bit = __builtin_ctzll(bits);
                            bits &= bits - 1;
                            int k = (w << 6) + bit;
                            if (k <= j) continue;
                            ++gen_4orb; ++total_4orb;

                            // Check 4-orbit free vertices!
                            Bitset5 free4;
                            free4.set_all_valid();
                            int oids4[4] = {0, compat0[i], compat0[j], compat0[k]};
                            for (int oi : oids4) {
                                for (int ww = 0; ww < W5; ++ww) free4.w[ww] &= ~orb_close[oi].w[ww];
                            }
                            int fc = free4.popcount();
                            if (fc > max_4orb_free) max_4orb_free = fc;
                            if (fc >= 8 && fc <= 512) {
                                std::vector<int> fv;
                                fv.reserve(fc);
                                for (int ww = 0; ww < W5; ++ww) {
                                    uint64_t bts = free4.w[ww];
                                    while (bts) {
                                        int bt = __builtin_ctzll(bts);
                                        bts &= bts - 1;
                                        fv.push_back((ww << 6) + bt);
                                    }
                                }
                                SmallMIS mis;
                                int ext = mis.solve(fv, global_best - 28 + 1, 200000);
                                if (28 + ext > global_best) {
                                    std::vector<int> sol;
                                    for (int oi : oids4) sol.insert(sol.end(), orb_verts[oi].begin(), orb_verts[oi].end());
                                    for (int idx : mis.best_sol) sol.push_back(mis.orig_ids[idx]);
                                    if (verify_indep5(sol)) {
                                        global_best = (int)sol.size();
                                        global_best_sol = sol;
                                        print_sol("4orb+ext", sol);
                                    }
                                }
                            }

                            // Check 4th vertex l > k (= 5-orbit code)
                            for (int ww = 0; ww < 8; ++ww) {
                                uint64_t bits4 = c3[ww] & adj[k][ww];
                                while (bits4) {
                                    int bit4 = __builtin_ctzll(bits4);
                                    bits4 &= bits4 - 1;
                                    int l = (ww << 6) + bit4;
                                    if (l <= k) continue;
                                    ++gen_5orb; ++total_5orb;

                                    std::vector<int> code;
                                    code.reserve(35);
                                    int oids5[5] = {0, compat0[i], compat0[j], compat0[k], compat0[l]};
                                    Bitset5 free5;
                                    free5.set_all_valid();
                                    for (int oi : oids5) {
                                        code.insert(code.end(), orb_verts[oi].begin(), orb_verts[oi].end());
                                        for (int u = 0; u < W5; ++u) free5.w[u] &= ~orb_close[oi].w[u];
                                    }
                                    int fc5 = free5.popcount();
                                    if (fc5 > 0) {
                                        // Instant 36+!
                                        for (int v = 0; v < N5; ++v) {
                                            if (free5.test(v)) { code.push_back(v); break; }
                                        }
                                        if (verify_indep5(code) && (int)code.size() > global_best) {
                                            global_best = (int)code.size();
                                            global_best_sol = code;
                                            print_sol("5orb+1", code);
                                        }
                                    }
                                    if (orbit5_codes.size() < 20000) orbit5_codes.push_back(std::move(code));
                                }
                            }
                        }
                    }
                }
            }
            if (gen_5orb > 0 || gen_4orb > 0) {
                std::cout << "[orb] g=(1,2,3," << a << "," << b << ") compat0=" << m
                          << " 4-orb=" << gen_4orb << " 5-orb=" << gen_5orb << "\n";
            }
        }
    }
    std::cout << "[orb] Total 4-orb=" << total_4orb << " (max_free=" << max_4orb_free
              << "), Total 5-orb=" << total_5orb << ", global_best=" << global_best << "\n";
    return orbit5_codes;
}

// Subtask 1B: Negation-symmetric pair graph ILS + LNS (origin + k pairs, or k pairs w/o origin)
static void run_neg_sym_search(bool with_origin, int time_sec, int& global_best, std::vector<int>& global_best_sol) {
    auto t0 = std::chrono::steady_clock::now();
    std::vector<std::pair<int, int>> pairs;
    for (int i = 0; i < N5; ++i) {
        std::array<int, 5> neg;
        for (int k = 0; k < 5; ++k) neg[k] = (7 - coords5[i][k]) % 7;
        int j = encode5(neg);
        if (i < j && !close_mask[i].test(j)) {
            if (!with_origin || !close_mask[0].test(i)) {
                pairs.push_back({i, j});
            }
        }
    }
    int P = (int)pairs.size();
    int PW = (P + 63) / 64;
    std::cout << "[neg-" << (with_origin ? "orig" : "no_orig") << "] pairs=" << P << "\n";

    // Build pair conflict bitsets
    std::vector<std::vector<uint64_t>> pclose(P, std::vector<uint64_t>(PW, 0ULL));
    for (int a = 0; a < P; ++a) {
        int u1 = pairs[a].first, u2 = pairs[a].second;
        for (int b = a; b < P; ++b) {
            int v1 = pairs[b].first;
            if (close_mask[u1].test(v1) || close_mask[u2].test(v1)) {
                pclose[a][b >> 6] |= (1ULL << (b & 63));
                pclose[b][a >> 6] |= (1ULL << (a & 63));
            }
        }
    }

    std::mt19937_64 rng(with_origin ? 1337ULL : 7331ULL);
    int best_p = 0;
    std::vector<int> best_pset;
    int iters = 0;
    while (std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count() < time_sec) {
        std::vector<int> S;
        std::vector<int> tight(P, 0);
        // Greedy randomized fill + ILS
        std::vector<int> order(P);
        std::iota(order.begin(), order.end(), 0);
        std::shuffle(order.begin(), order.end(), rng);
        for (int v : order) {
            if (tight[v] == 0) {
                S.push_back(v);
                for (int b = 0; b < P; ++b) {
                    if ((pclose[v][b >> 6] >> (b & 63)) & 1ULL) ++tight[b];
                }
            }
        }
        // ILS swaps
        for (int step = 0; step < 500; ++step) {
            // Find 1-tight vertices
            std::vector<std::vector<int>> one_by_s(S.size());
            std::vector<int> free_v;
            for (int v = 0; v < P; ++v) {
                if (tight[v] == 0) free_v.push_back(v);
            }
            while (!free_v.empty()) {
                int v = free_v[rng() % free_v.size()];
                if (tight[v] == 0) {
                    S.push_back(v);
                    for (int b = 0; b < P; ++b) if ((pclose[v][b >> 6] >> (b & 63)) & 1ULL) ++tight[b];
                }
                free_v.clear();
                for (int x = 0; x < P; ++x) if (tight[x] == 0) free_v.push_back(x);
            }
            if ((int)S.size() > best_p) {
                best_p = (int)S.size();
                best_pset = S;
            }
            int word_cnt = (with_origin ? 1 : 0) + 2 * (int)S.size();
            if (word_cnt > global_best) {
                std::vector<int> sol;
                if (with_origin) sol.push_back(0);
                for (int pi : S) { sol.push_back(pairs[pi].first); sol.push_back(pairs[pi].second); }
                if (verify_indep5(sol)) {
                    global_best = word_cnt;
                    global_best_sol = sol;
                    print_sol(with_origin ? "neg-orig" : "neg-no_orig", sol);
                }
            }
            // Kick: remove 1 or 2 random elements and add a 1-tight or random vertex
            std::vector<int> cand1;
            for (int v = 0; v < P; ++v) if (tight[v] == 1) cand1.push_back(v);
            if (!cand1.empty()) {
                int v = cand1[rng() % cand1.size()];
                // Find unique blocker in S
                int bi = -1;
                for (int i = 0; i < (int)S.size(); ++i) {
                    if ((pclose[S[i]][v >> 6] >> (v & 63)) & 1ULL) { bi = i; break; }
                }
                if (bi >= 0) {
                    int rem = S[bi];
                    S[bi] = v;
                    for (int b = 0; b < P; ++b) {
                        bool had = (pclose[rem][b >> 6] >> (b & 63)) & 1ULL;
                        bool now = (pclose[v][b >> 6] >> (b & 63)) & 1ULL;
                        tight[b] += (int)now - (int)had;
                    }
                }
            } else if (!S.empty()) {
                int bi = rng() % S.size();
                int rem = S[bi];
                S[bi] = S.back(); S.pop_back();
                for (int b = 0; b < P; ++b) if ((pclose[rem][b >> 6] >> (b & 63)) & 1ULL) --tight[b];
            }
        }
        ++iters;
    }
    int best_words = (with_origin ? 1 : 0) + 2 * best_p;
    std::cout << "[neg-" << (with_origin ? "orig" : "no_orig") << "] iters=" << iters
              << " best_pairs=" << best_p << " (" << best_words << " words)\n";
}

// Subtask 1C: Full V5 ILS + Exact LNS starting from 5-orbit codes
static void run_v5_lns_and_ils(const std::vector<std::vector<int>>& seeds5, int time_sec,
                               int& global_best, std::vector<int>& global_best_sol) {
    auto t0 = std::chrono::steady_clock::now();
    std::mt19937_64 rng(424242ULL);
    uint64_t lns_trials = 0, ils_steps = 0;
    int max_seen = global_best;

    // 1. Exact LNS destroying k=7..13 words from diverse 5-orbit codes
    std::vector<int> k_choices = {7, 8, 9, 10, 11, 12};
    while (std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count() < time_sec * 0.6) {
        const auto& base = seeds5[rng() % seeds5.size()];
        int k = k_choices[rng() % k_choices.size()];
        std::vector<int> perm(base.size());
        std::iota(perm.begin(), perm.end(), 0);
        // Half the time destroy an entire 7-word orbit + (k-7) more!
        std::vector<bool> drop(base.size(), false);
        if (rng() % 2 == 0) {
            int orb = rng() % 5;
            for (int t = 0; t < 7; ++t) drop[orb * 7 + t] = true;
            int extra = k - 7;
            while (extra > 0) {
                int idx = rng() % base.size();
                if (!drop[idx]) { drop[idx] = true; --extra; }
            }
        } else {
            std::shuffle(perm.begin(), perm.end(), rng);
            for (int i = 0; i < k; ++i) drop[perm[i]] = true;
        }
        Bitset5 free_mask;
        free_mask.set_all_valid();
        std::vector<int> kept;
        for (size_t i = 0; i < base.size(); ++i) {
            if (!drop[i]) {
                kept.push_back(base[i]);
                for (int w = 0; w < W5; ++w) free_mask.w[w] &= ~close_mask[base[i]].w[w];
            }
        }
        int fc = free_mask.popcount();
        if (fc >= k + 1 && fc <= 512) {
            std::vector<int> fv;
            fv.reserve(fc);
            for (int w = 0; w < W5; ++w) {
                uint64_t bts = free_mask.w[w];
                while (bts) {
                    int bt = __builtin_ctzll(bts);
                    bts &= bts - 1;
                    fv.push_back((w << 6) + bt);
                }
            }
            SmallMIS mis;
            int got = mis.solve(fv, k + 1, 150000);
            if ((int)kept.size() + got > max_seen) {
                std::vector<int> sol = kept;
                for (int idx : mis.best_sol) sol.push_back(mis.orig_ids[idx]);
                if (verify_indep5(sol)) {
                    max_seen = (int)sol.size();
                    global_best = max_seen;
                    global_best_sol = sol;
                    print_sol("LNS", sol);
                }
            }
        }
        ++lns_trials;
    }

    // 2. Full V5 bit-parallel ILS with (1,1), (1,2), and (2,3) swaps
    std::vector<int> tight(N5);
    while (std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count() < time_sec) {
        std::vector<int> S = seeds5[rng() % seeds5.size()];
        std::fill(tight.begin(), tight.end(), 0);
        for (int u : S) {
            for (int v = 0; v < N5; ++v) if (close_mask[u].test(v)) ++tight[v];
        }
        for (int step = 0; step < 3000; ++step) {
            // Greedy fill
            bool added = true;
            while (added) {
                added = false;
                for (int v = 0; v < N5; ++v) {
                    if (tight[v] == 0) {
                        S.push_back(v);
                        for (int w = 0; w < N5; ++w) if (close_mask[v].test(w)) ++tight[w];
                        added = true;
                        break;
                    }
                }
            }
            if ((int)S.size() > max_seen && verify_indep5(S)) {
                max_seen = (int)S.size();
                global_best = max_seen;
                global_best_sol = S;
                print_sol("ILS", S);
            }
            // Collect 1-tight vertices
            std::vector<int> one_t;
            one_t.reserve(256);
            for (int v = 0; v < N5; ++v) if (tight[v] == 1) one_t.push_back(v);
            if (!one_t.empty()) {
                int v = one_t[rng() % one_t.size()];
                int bi = -1;
                for (int i = 0; i < (int)S.size(); ++i) if (close_mask[S[i]].test(v)) { bi = i; break; }
                int rem = S[bi];
                S[bi] = v;
                for (int w = 0; w < N5; ++w) {
                    bool had = close_mask[rem].test(w);
                    bool now = close_mask[v].test(w);
                    if (had != now) tight[w] += (now ? 1 : -1);
                }
            } else {
                // Random (2, k) kick
                for (int r = 0; r < 2 && !S.empty(); ++r) {
                    int bi = rng() % S.size();
                    int rem = S[bi];
                    S[bi] = S.back(); S.pop_back();
                    for (int w = 0; w < N5; ++w) if (close_mask[rem].test(w)) --tight[w];
                }
            }
            ++ils_steps;
        }
    }
    std::cout << "[v5-lns-ils] lns_trials=" << lns_trials << " ils_steps=" << ils_steps
              << " max_seen=" << max_seen << "\n";
}

int main() {
    auto t0 = std::chrono::steady_clock::now();
    init_graph5();
    std::cout << "[init] N5=16807 conflict bitsets built in "
              << std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count() << "s\n";

    int global_best = 0;
    std::vector<int> global_best_sol;

    auto seeds5 = run_orbit_search(global_best, global_best_sol);
    if (global_best < 35 && !seeds5.empty()) {
        global_best = 35;
        global_best_sol = seeds5[0];
    }

    run_neg_sym_search(true, 10, global_best, global_best_sol);
    run_neg_sym_search(false, 10, global_best, global_best_sol);
    run_v5_lns_and_ils(seeds5, 25, global_best, global_best_sol);

    std::cout << "[FINAL d=5] global_best=" << global_best << " valid=" << verify_indep5(global_best_sol) << "\n";
    std::ofstream out("/mnt/nvme2tb/shannon_struct_scratch/compl/d5_best.json");
    out << "{\"d\": 5, \"size\": " << global_best_sol.size() << ", \"words\": [\n";
    for (size_t i = 0; i < global_best_sol.size(); ++i) {
        auto c = coords5[global_best_sol[i]];
        out << "  [" << c[0] << ", " << c[1] << ", " << c[2] << ", " << c[3] << ", " << c[4] << "]";
        out << (i + 1 < global_best_sol.size() ? ",\n" : "\n");
    }
    out << "]}\n";
    return 0;
}
