// Stage 3 v3: Comprehensive d=5 ValidTuple & PartGadget Search
// 1) Check all 560 5-orbit codes + greedy (1,1)-swap SA to minimize |N[s] cap N[q]| (target 243..768).
// 2) For smallest |F| (b=1) and small multi-port (b=2..7), search X in V5 \ F via:
//    (a) All 3840*16807 Aut(C7^5) images of S35 and C35 (4orb+ext)
//    (b) Exact LNS inside V5 \ F destroying k=4..10 words from best 34-word subset!
// Compile: g++ -O3 -march=native -std=c++17 search/lower/compl_d5_blowup.cpp -o /mnt/nvme2tb/shannon_struct_scratch/compl/compl_d5_blowup

#include <algorithm>
#include <array>
#include <chrono>
#include <cmath>
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
    inline void set(int i) { w[i >> 6] |= (1ULL << (i & 63)); }
    inline bool test(int i) const { return (w[i >> 6] >> (i & 63)) & 1ULL; }
    inline int popcount() const {
        int s = 0;
        for (int i = 0; i < W5; ++i) s += __builtin_popcountll(w[i]);
        return s;
    }
};

static std::array<std::array<int, 5>, N5> coords5;
static std::vector<Bitset5> close5;

static int encode5(const std::array<int, 5>& a) {
    int id = 0;
    for (int k = 0; k < 5; ++k) id = id * 7 + a[k];
    return id;
}

static void init5() {
    close5.resize(N5);
    for (int i = 0; i < N5; ++i) {
        int tmp = i;
        for (int k = 4; k >= 0; --k) { coords5[i][k] = tmp % 7; tmp /= 7; }
    }
    static const int cd[5] = {0, 2, 3, 4, 5};
    for (int u = 0; u < N5; ++u) {
        close5[u].clear();
        const auto& a = coords5[u];
        for (int d0 : cd) { int c0 = (a[0]+d0)%7;
        for (int d1 : cd) { int c1 = (a[1]+d1)%7;
        for (int d2 : cd) { int c2 = (a[2]+d2)%7;
        for (int d3 : cd) { int c3 = (a[3]+d3)%7;
            int base = (((c0*7+c1)*7+c2)*7+c3)*7;
            for (int d4 : cd) close5[u].set(base + (a[4]+d4)%7);
        }}}}
    }
}

static bool verify_indep5(const std::vector<int>& S) {
    for (size_t i = 0; i < S.size(); ++i)
        for (size_t j = i + 1; j < S.size(); ++j)
            if (close5[S[i]].test(S[j])) return false;
    return true;
}

struct PrivPair { int s_idx, s, q, forb_sz; };

static std::vector<PrivPair> find_privs(const std::vector<int>& I) {
    std::vector<int> tight(N5, 0), uniq_s(N5, -1);
    for (int si = 0; si < (int)I.size(); ++si) {
        int u = I[si];
        for (int w = 0; w < W5; ++w) {
            uint64_t b = close5[u].w[w];
            while (b) { int bit = __builtin_ctzll(b); b &= b - 1; int v = (w<<6)+bit; ++tight[v]; uniq_s[v] = si; }
        }
    }
    std::vector<PrivPair> res;
    for (int v = 0; v < N5; ++v) {
        if (tight[v] == 1) {
            int si = uniq_s[v], s = I[si];
            if (v != s) {
                int fsz = 0;
                for (int w = 0; w < W5; ++w) fsz += __builtin_popcountll(close5[s].w[w] & close5[v].w[w]);
                res.push_back({si, s, v, fsz});
            }
        }
    }
    std::sort(res.begin(), res.end(), [](const PrivPair& a, const PrivPair& b) { return a.forb_sz < b.forb_sz; });
    return res;
}

// Fast exact MIS on up to 512 vertices
struct SmallMIS {
    int n;
    std::vector<int> orig_ids;
    std::vector<std::array<uint64_t, 8>> ind_adj;
    int best_sz;
    std::vector<int> best_sol, cur_sol;
    uint64_t nodes = 0, limit = 200000;

    void dfs(const std::array<uint64_t, 8>& cand, int sz) {
        if (nodes > limit) return;
        int rem = 0;
        for (int k = 0; k < 8; ++k) rem += __builtin_popcountll(cand[k]);
        if (sz + rem <= best_sz) return;
        if (rem == 0) { if (sz > best_sz) { best_sz = sz; best_sol = cur_sol; } return; }
        int v = -1;
        for (int k = 0; k < 8; ++k) if (cand[k]) { v = (k<<6) + __builtin_ctzll(cand[k]); break; }
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

    int solve(const std::vector<int>& verts, int target_min, uint64_t lim = 200000) {
        n = (int)verts.size();
        if (n > 512 || n < target_min) return -1;
        std::vector<std::pair<int, int>> deg(n);
        for (int i = 0; i < n; ++i) {
            int c = 0;
            for (int j = 0; j < n; ++j) if (i != j && !close5[verts[i]].test(verts[j])) ++c;
            deg[i] = {c, i};
        }
        std::sort(deg.begin(), deg.end());
        orig_ids.resize(n);
        for (int i = 0; i < n; ++i) orig_ids[i] = verts[deg[i].second];
        ind_adj.assign(n, {});
        for (int i = 0; i < n; ++i) {
            ind_adj[i].fill(0ULL);
            for (int j = 0; j < n; ++j)
                if (i != j && !close5[orig_ids[i]].test(orig_ids[j])) ind_adj[i][j >> 6] |= (1ULL << (j & 63));
        }
        std::array<uint64_t, 8> cand{};
        for (int i = 0; i < n; ++i) cand[i >> 6] |= (1ULL << (i & 63));
        best_sz = target_min - 1;
        best_sol.clear(); cur_sol.clear(); nodes = 0; limit = lim;
        dfs(cand, 0);
        return best_sz;
    }
};

static std::vector<std::vector<int>> gen_560_codes() {
    std::array<int, 5> g = {1, 2, 3, 1, 2};
    std::array<std::vector<int>, 2401> orb_verts;
    std::vector<Bitset5> orb_close(2401);
    for (int oid = 0; oid < 2401; ++oid) {
        int tmp = oid; std::array<int, 5> base{};
        for (int k = 4; k >= 1; --k) { base[k] = tmp % 7; tmp /= 7; }
        orb_close[oid].clear();
        for (int t = 0; t < 7; ++t) {
            std::array<int, 5> w;
            for (int k = 0; k < 5; ++k) w[k] = (base[k] + t * g[k]) % 7;
            int vid = encode5(w);
            orb_verts[oid].push_back(vid);
            for (int u = 0; u < W5; ++u) orb_close[oid].w[u] |= close5[vid].w[u];
        }
    }
    std::vector<int> compat0;
    for (int oid = 1; oid < 2401; ++oid) {
        bool ok = true;
        for (int v : orb_verts[oid]) if (orb_close[0].test(v)) { ok = false; break; }
        if (ok) compat0.push_back(oid);
    }
    int m = (int)compat0.size();
    std::vector<std::array<uint64_t, 8>> adj(m);
    for (int i = 0; i < m; ++i) {
        adj[i].fill(0ULL);
        for (int j = i + 1; j < m; ++j) {
            bool ok = true;
            for (int v : orb_verts[compat0[j]]) if (orb_close[compat0[i]].test(v)) { ok = false; break; }
            if (ok) adj[i][j >> 6] |= (1ULL << (j & 63));
        }
    }
    std::vector<std::vector<int>> codes;
    for (int i = 0; i < m; ++i) {
        for (int j = i + 1; j < m; ++j) {
            if (!((adj[i][j >> 6] >> (j & 63)) & 1ULL)) continue;
            std::array<uint64_t, 8> c3;
            for (int w = 0; w < 8; ++w) c3[w] = adj[i][w] & adj[j][w];
            for (int w = 0; w < 8; ++w) {
                uint64_t b3 = c3[w];
                while (b3) {
                    int bit = __builtin_ctzll(b3); b3 &= b3 - 1;
                    int k = (w << 6) + bit; if (k <= j) continue;
                    for (int ww = 0; ww < 8; ++ww) {
                        uint64_t b4 = c3[ww] & adj[k][ww];
                        while (b4) {
                            int bit4 = __builtin_ctzll(b4); b4 &= b4 - 1;
                            int l = (ww << 6) + bit4; if (l <= k) continue;
                            std::vector<int> code;
                            int oids[5] = {0, compat0[i], compat0[j], compat0[k], compat0[l]};
                            for (int oi : oids) code.insert(code.end(), orb_verts[oi].begin(), orb_verts[oi].end());
                            codes.push_back(std::move(code));
                        }
                    }
                }
            }
        }
    }
    return codes;
}

// Fast exact Aut(C7^5) scan of base_X against F: returns max_c and witness shifts
static int scan_aut_max_c(const std::vector<int>& base_X, const Bitset5& forb,
                          const Bitset5& n0, const Bitset5& n1,
                          std::vector<int>& out_X, int& out_d, int& out_h, int& out_v,
                          int max_maps = 3840) {
    std::vector<std::array<int, 5>> fcoords;
    for (int v = 0; v < N5; ++v) if (forb.test(v)) fcoords.push_back(coords5[v]);
    int F = (int)fcoords.size();
    int sz = (int)base_X.size();

    std::array<int, 5> perm = {0, 1, 2, 3, 4};
    std::vector<int> hits(N5);
    int best_c = -1;
    int map_idx = 0;

    do {
        for (int mask = 0; mask < 32; ++mask) {
            if (++map_idx > max_maps) break;
            std::array<int, 5> sgn;
            for (int k = 0; k < 5; ++k) sgn[k] = ((mask >> k) & 1) ? 6 : 1;
            std::array<std::array<int, 5>, 35> yc;
            for (int i = 0; i < sz; ++i) {
                const auto& c = coords5[base_X[i]];
                for (int k = 0; k < 5; ++k) yc[i][k] = (c[perm[k]] * sgn[k]) % 7;
            }
            std::fill(hits.begin(), hits.end(), 0);
            for (int i = 0; i < sz; ++i) {
                const auto& y = yc[i];
                for (int fi = 0; fi < F; ++fi) {
                    const auto& fc = fcoords[fi];
                    int t = ((((fc[0]-y[0]+7)%7)*7 + (fc[1]-y[1]+7)%7)*7 + (fc[2]-y[2]+7)%7)*7;
                    t = (t + (fc[3]-y[3]+7)%7)*7 + (fc[4]-y[4]+7)%7;
                    ++hits[t];
                }
            }
            for (int t = 0; t < N5; ++t) {
                int c = sz - hits[t];
                if (c > best_c) {
                    best_c = c;
                    out_X.clear();
                    out_d = out_h = out_v = 0;
                    const auto& tc = coords5[t];
                    for (int i = 0; i < sz; ++i) {
                        std::array<int, 5> xc;
                        for (int k = 0; k < 5; ++k) xc[k] = (yc[i][k] + tc[k]) % 7;
                        int xv = encode5(xc);
                        if (forb.test(xv)) continue;
                        out_X.push_back(xv);
                        bool i0 = n0.test(xv), i1 = n1.test(xv);
                        if (!i0 && !i1) ++out_d;
                        else if (i0 && !i1) ++out_h;
                        else if (i1 && !i0) ++out_v;
                    }
                    if (best_c == sz && out_d >= 15) return best_c;
                }
            }
        }
        if (map_idx > max_maps) break;
    } while (std::next_permutation(perm.begin(), perm.end()));
    return best_c;
}

// LNS inside V5 \ F starting from a good size-34 subset
static std::vector<int> lns_avoid_F(const Bitset5& forb, const std::vector<int>& seed_34, int target_c, int time_ms) {
    auto t0 = std::chrono::steady_clock::now();
    std::mt19937_64 rng(123456ULL);
    std::vector<int> cur = seed_34;
    if ((int)cur.size() >= target_c) return cur;

    std::vector<int> ks = {4, 6, 8, 10};
    int trials = 0;
    while (std::chrono::duration<double, std::milli>(std::chrono::steady_clock::now() - t0).count() < time_ms) {
        int k = ks[rng() % ks.size()];
        if (k >= (int)cur.size()) continue;
        std::vector<int> perm(cur.size());
        std::iota(perm.begin(), perm.end(), 0);
        std::shuffle(perm.begin(), perm.end(), rng);
        Bitset5 allow;
        for (int w = 0; w < W5; ++w) allow.w[w] = ~forb.w[w];
        int rem = N5 % 64;
        if (rem) allow.w[W5 - 1] &= (1ULL << rem) - 1ULL;

        std::vector<int> kept;
        for (size_t i = k; i < perm.size(); ++i) {
            int u = cur[perm[i]];
            kept.push_back(u);
            for (int w = 0; w < W5; ++w) allow.w[w] &= ~close5[u].w[w];
        }
        int fc = allow.popcount();
        if (fc >= target_c - (int)kept.size() && fc <= 512) {
            std::vector<int> fv;
            fv.reserve(fc);
            for (int w = 0; w < W5; ++w) {
                uint64_t b = allow.w[w];
                while (b) { int bit = __builtin_ctzll(b); b &= b - 1; fv.push_back((w << 6) + bit); }
            }
            SmallMIS mis;
            int got = mis.solve(fv, target_c - (int)kept.size(), 100000);
            if ((int)kept.size() + got >= target_c) {
                std::vector<int> sol = kept;
                for (int idx : mis.best_sol) sol.push_back(mis.orig_ids[idx]);
                if (verify_indep5(sol)) return sol;
            }
        }
        ++trials;
    }
    return cur;
}

int main() {
    auto t0 = std::chrono::steady_clock::now();
    init5();
    auto codes560 = gen_560_codes();
    std::cout << "[init] 560 5-orbit codes generated in "
              << std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count() << "s\n";

    // Also include 4orb+ext C35!
    std::vector<int> C35;
    std::vector<std::array<int, 5>> c35_raw = {
        {0,0,0,0,0},{1,2,3,1,2},{2,4,6,2,4},{3,6,2,3,6},{4,1,5,4,1},{5,3,1,5,3},{6,5,4,6,5},
        {0,0,0,1,2},{1,2,3,2,4},{2,4,6,3,6},{3,6,2,4,1},{4,1,5,5,3},{5,3,1,6,5},{6,5,4,0,0},
        {0,1,0,4,2},{1,3,3,5,4},{2,5,6,6,6},{3,0,2,0,1},{4,2,5,1,3},{5,4,1,2,5},{6,6,4,3,0},
        {0,4,6,3,0},{1,6,2,4,2},{2,1,5,5,4},{3,3,1,6,6},{4,5,4,0,1},{5,0,0,1,3},{6,2,3,2,5},
        {0,5,6,0,2},{1,0,2,1,4},{2,2,5,0,6},{3,4,1,1,1},{4,6,4,2,3},{5,1,0,3,5},{6,3,3,4,0}
    };
    for (auto& a : c35_raw) C35.push_back(encode5(a));

    // Check min_forb across all 560 codes + C35 + random (1,1)-swap walks!
    int global_min_forb = 99999;
    std::vector<int> min_forb_I;
    PrivPair min_forb_pp{0,0,0,99999};

    for (size_t ci = 0; ci < codes560.size(); ++ci) {
        auto pps = find_privs(codes560[ci]);
        if (!pps.empty() && pps[0].forb_sz < global_min_forb) {
            global_min_forb = pps[0].forb_sz;
            min_forb_I = codes560[ci];
            min_forb_pp = pps[0];
            std::cout << "[560 code #" << ci << "] min_forb=" << global_min_forb << "\n";
        }
    }
    {
        auto pps = find_privs(C35);
        std::cout << "[C35] privs=" << pps.size() << " min_forb=" << pps[0].forb_sz << "\n";
        if (pps[0].forb_sz < global_min_forb) {
            global_min_forb = pps[0].forb_sz; min_forb_I = C35; min_forb_pp = pps[0];
        }
    }

    // Now do (1,1)-swap walks from diverse seeds specifically trying to get min_forb < 1024!
    std::mt19937_64 rng(20261127ULL);
    for (int restart = 0; restart < 30; ++restart) {
        std::vector<int> cur = (restart == 0) ? C35 : codes560[rng() % codes560.size()];
        std::vector<int> tight(N5, 0);
        for (int u : cur)
            for (int w = 0; w < W5; ++w) {
                uint64_t b = close5[u].w[w];
                while (b) { int bit = __builtin_ctzll(b); b &= b - 1; ++tight[(w<<6)+bit]; }
            }
        for (int step = 0; step < 400; ++step) {
            std::vector<int> c1;
            for (int v = 0; v < N5; ++v) if (tight[v] == 1) c1.push_back(v);
            if (c1.empty()) break;
            int v = c1[rng() % c1.size()];
            int bi = -1;
            for (int i = 0; i < 35; ++i) if (close5[cur[i]].test(v)) { bi = i; break; }
            int rem = cur[bi];
            cur[bi] = v;
            for (int w = 0; w < W5; ++w) {
                uint64_t diff = close5[rem].w[w] ^ close5[v].w[w];
                while (diff) {
                    int bit = __builtin_ctzll(diff); diff &= diff - 1;
                    tight[(w<<6)+bit] += ((close5[v].w[w] >> bit) & 1ULL) ? 1 : -1;
                }
            }
            if (step % 5 == 0) {
                auto pps = find_privs(cur);
                if (!pps.empty() && pps[0].forb_sz < global_min_forb) {
                    global_min_forb = pps[0].forb_sz;
                    min_forb_I = cur;
                    min_forb_pp = pps[0];
                    std::cout << "[walk r=" << restart << " s=" << step << "] NEW min_forb=" << global_min_forb << "\n";
                }
            }
        }
    }
    std::cout << "[phase1 done] global_min_forb=" << global_min_forb << " elapsed="
              << std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count() << "s\n";

    // Phase 2: Test min_forb_I (b=1) + multi-port b=2..6 on C35 and min_forb_I!
    struct Win { int a, b, c, d, h, v; std::vector<int> I, P0, P1, X; };
    Win best_win{0,0,0,0,0,0,{},{},{},{}};
    double best_sc = 1225.0; // 35^2

    auto try_gadget = [&](const char* label, const std::vector<int>& I, const std::vector<int>& P0, const std::vector<int>& P1, int lns_ms) {
        int b = (int)P0.size();
        Bitset5 n0{}, n1{}, forb{};
        for (int p : P0) for (int w = 0; w < W5; ++w) n0.w[w] |= close5[p].w[w];
        for (int p : P1) for (int w = 0; w < W5; ++w) n1.w[w] |= close5[p].w[w];
        for (int w = 0; w < W5; ++w) forb.w[w] = n0.w[w] & n1.w[w];
        int fsz = forb.popcount();

        std::vector<int> X_aut;
        int d = 0, h = 0, v = 0;
        int c_aut = scan_aut_max_c(C35, forb, n0, n1, X_aut, d, h, v, 3840);
        double sc = (35.0 - b)*(35.0 - b) + 2.0 * b * c_aut;
        std::cout << "[" << label << " aut(C35) b=" << b << " |F|=" << fsz << "] c=" << c_aut
                  << " (d=" << d << ",h=" << h << ",v=" << v << ") a2=" << (long long)sc << std::endl;

        std::vector<int> best_X = X_aut;
        int best_c = c_aut;
        if (best_c < 35 && lns_ms > 0) {
            auto X_lns = lns_avoid_F(forb, X_aut, 35, lns_ms);
            if ((int)X_lns.size() > best_c) {
                best_X = X_lns;
                best_c = (int)X_lns.size();
                d = h = v = 0;
                for (int x : best_X) {
                    bool i0 = n0.test(x), i1 = n1.test(x);
                    if (!i0 && !i1) ++d;
                    else if (i0 && !i1) ++h;
                    else if (i1 && !i0) ++v;
                }
                sc = (35.0 - b)*(35.0 - b) + 2.0 * b * best_c;
                std::cout << "[" << label << " LNS b=" << b << "] c=" << best_c
                          << " (d=" << d << ",h=" << h << ",v=" << v << ") a2=" << (long long)sc << std::endl;
            }
        }
        if (sc > best_sc + 1e-9) {
            best_sc = sc;
            best_win = {35, b, best_c, d, h, v, I, P0, P1, best_X};
        }
    };

    try_gadget("minF", min_forb_I, {min_forb_pp.s}, {min_forb_pp.q}, 6000);

    // Also test b=2, 3, 4, 5 greedy port subsets of min_forb_I and C35!
    for (const auto& cand_I : {min_forb_I, C35, codes560[0]}) {
        auto pps = find_privs(cand_I);
        std::vector<int> P0, P1;
        std::vector<bool> used_s(35, false);
        for (const auto& pp : pps) {
            if (used_s[pp.s_idx]) continue;
            bool ok0 = true;
            for (size_t i = 0; i < P0.size(); ++i)
                if (close5[pp.s].test(P0[i]) || close5[pp.q].test(P1[i])) { ok0 = false; break; }
            if (ok0) { used_s[pp.s_idx] = true; P0.push_back(pp.s); P1.push_back(pp.q); }
            else {
                bool ok1 = true;
                for (size_t i = 0; i < P0.size(); ++i)
                    if (close5[pp.q].test(P0[i]) || close5[pp.s].test(P1[i])) { ok1 = false; break; }
                if (ok1) { used_s[pp.s_idx] = true; P0.push_back(pp.q); P1.push_back(pp.s); }
            }
            if (P0.size() == 3 || P0.size() == 5) {
                try_gadget("multi", cand_I, P0, P1, 3000);
            }
        }
    }

    if (best_win.a > 0) {
        std::ofstream out("/mnt/nvme2tb/shannon_struct_scratch/compl/d5_gadget_best.json");
        auto write_list = [&](const char* name, const std::vector<int>& lst) {
            out << "  \"" << name << "\": [";
            for (size_t i = 0; i < lst.size(); ++i) {
                auto c = coords5[lst[i]];
                out << "[" << c[0] << "," << c[1] << "," << c[2] << "," << c[3] << "," << c[4] << "]";
                if (i + 1 < lst.size()) out << ",";
            }
            out << "]";
        };
        out << "{\n";
        out << "  \"a\": " << best_win.a << ", \"b\": " << best_win.b << ", \"c\": " << best_win.c
            << ", \"d\": " << best_win.d << ", \"h\": " << best_win.h << ", \"v\": " << best_win.v << ",\n";
        write_list("I", best_win.I); out << ",\n";
        write_list("P0", best_win.P0); out << ",\n";
        write_list("P1", best_win.P1); out << ",\n";
        write_list("X", best_win.X); out << "\n}\n";
        std::cout << "[WINNER] Saved d5_gadget_best.json! (" << best_win.a << "," << best_win.b << ","
                  << best_win.c << "," << best_win.d << "," << best_win.h << "," << best_win.v
                  << ") a2=" << (long long)best_sc << " rate2=" << std::pow(best_sc, 0.1) << "\n";
    } else {
        std::cout << "[DONE] No d=5 gadget beat 35^2 yet.\n";
    }
    return 0;
}
