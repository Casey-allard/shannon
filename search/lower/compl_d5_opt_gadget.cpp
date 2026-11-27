// Optimize d=5 ValidTuple & PartGadget across b=1 (all pairs), b=2, b=3, b=4 with Aut(C7^5) + LNS
// Compile: g++ -O3 -march=native -std=c++17 search/lower/compl_d5_opt_gadget.cpp -o /mnt/nvme2tb/shannon_struct_scratch/compl/compl_d5_opt_gadget

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
static constexpr int W5 = (N5 + 63) / 64;

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

struct SmallMIS {
    int n;
    std::vector<int> orig_ids;
    std::vector<std::array<uint64_t, 8>> ind_adj;
    int best_sz;
    std::vector<int> best_sol, cur_sol;
    uint64_t nodes = 0, limit = 150000;

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

    int solve(const std::vector<int>& verts, int target_min, uint64_t lim = 150000) {
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

struct GadgetResult {
    int a, b, c, d, h, v;
    double score2;
    std::vector<int> I, P0, P1, X;
};

static std::vector<int> lns_avoid_F(const Bitset5& forb, const std::vector<int>& seed, int target_c, int time_ms) {
    auto t0 = std::chrono::steady_clock::now();
    std::mt19937_64 rng(777888ULL);
    std::vector<int> cur = seed;
    if ((int)cur.size() >= target_c) return cur;
    std::vector<int> ks = {4, 6, 8, 10, 12};
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
    }
    return cur;
}

static void scan_and_lns(const char* label, const std::vector<int>& I,
                         const std::vector<int>& P0, const std::vector<int>& P1,
                         const std::vector<int>& base_X, GadgetResult& best_d, GadgetResult& best_sc,
                         int max_maps, int lns_ms) {
    int b = (int)P0.size();
    Bitset5 n0{}, n1{}, forb{};
    for (int p : P0) for (int w = 0; w < W5; ++w) n0.w[w] |= close5[p].w[w];
    for (int p : P1) for (int w = 0; w < W5; ++w) n1.w[w] |= close5[p].w[w];
    for (int w = 0; w < W5; ++w) forb.w[w] = n0.w[w] & n1.w[w];
    std::vector<std::array<int, 5>> fcoords;
    for (int v = 0; v < N5; ++v) if (forb.test(v)) fcoords.push_back(coords5[v]);
    int F = (int)fcoords.size();
    int sz = (int)base_X.size();

    std::array<int, 5> perm = {0, 1, 2, 3, 4};
    std::vector<int> hits(N5);
    int map_idx = 0;
    int best_c_aut = 0;
    std::vector<int> best_X_aut;

    do {
        for (int mask = 0; mask < 32; ++mask) {
            if (++map_idx > max_maps) goto done_aut;
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
                if (c > best_c_aut || (c == best_c_aut && c >= 34)) {
                    const auto& tc = coords5[t];
                    std::vector<int> X;
                    X.reserve(c);
                    int d = 0, h = 0, v = 0;
                    for (int i = 0; i < sz; ++i) {
                        std::array<int, 5> xc;
                        for (int k = 0; k < 5; ++k) xc[k] = (yc[i][k] + tc[k]) % 7;
                        int xv = encode5(xc);
                        if (forb.test(xv)) continue;
                        X.push_back(xv);
                        bool i0 = n0.test(xv), i1 = n1.test(xv);
                        if (!i0 && !i1) ++d;
                        else if (i0 && !i1) ++h;
                        else if (i1 && !i0) ++v;
                    }
                    if (c > best_c_aut) { best_c_aut = c; best_X_aut = X; }
                    double sc = (35.0 - b)*(35.0 - b) + 2.0 * b * c;
                    if (sc > best_sc.score2 + 1e-9 || (std::abs(sc - best_sc.score2) < 1e-9 && d > best_sc.d)) {
                        best_sc = {35, b, c, d, h, v, sc, I, P0, P1, X};
                        std::cout << "[" << label << " BEST-SC] (35," << b << "," << c << "," << d << "," << h << "," << v
                                  << ") a2=" << (long long)sc << std::endl;
                    }
                    if (b == 1 && c == 35 && d > best_d.d) {
                        best_d = {35, b, c, d, h, v, sc, I, P0, P1, X};
                        std::cout << "[" << label << " MAX-D] (35,1,35, d=" << d << ", h=" << h << ", v=" << v << ")" << std::endl;
                    }
                }
            }
        }
    } while (std::next_permutation(perm.begin(), perm.end()));
done_aut:
    std::cout << "[" << label << " b=" << b << " |F|=" << F << "] best_c_aut=" << best_c_aut << std::endl;
    if (lns_ms > 0 && best_c_aut < 35 && !best_X_aut.empty()) {
        int needed = (b == 1) ? 35 : (b <= 2 ? 35 : 34);
        auto X_lns = lns_avoid_F(forb, best_X_aut, needed, lns_ms);
        int c = (int)X_lns.size();
        if (c > best_c_aut) {
            int d = 0, h = 0, v = 0;
            for (int xv : X_lns) {
                bool i0 = n0.test(xv), i1 = n1.test(xv);
                if (!i0 && !i1) ++d; else if (i0 && !i1) ++h; else if (i1 && !i0) ++v;
            }
            double sc = (35.0 - b)*(35.0 - b) + 2.0 * b * c;
            std::cout << "[" << label << " LNS] (35," << b << "," << c << "," << d << "," << h << "," << v
                      << ") a2=" << (long long)sc << std::endl;
            if (sc > best_sc.score2 + 1e-9) best_sc = {35, b, c, d, h, v, sc, I, P0, P1, X_lns};
        }
    }
}

int main() {
    init5();
    std::vector<int> S35, C35;
    std::array<int, 5> g5 = {1, 2, 3, 1, 2};
    std::vector<std::array<int, 5>> seeds5 = {{0,0,0,0,0},{0,0,0,1,1},{0,0,1,4,3},{0,2,0,2,1},{0,2,1,1,4}};
    for (const auto& sd : seeds5)
        for (int t = 0; t < 7; ++t)
            S35.push_back(encode5({(sd[0]+t*g5[0])%7, (sd[1]+t*g5[1])%7, (sd[2]+t*g5[2])%7, (sd[3]+t*g5[3])%7, (sd[4]+t*g5[4])%7}));

    std::vector<std::array<int, 5>> c35_raw = {
        {0,0,0,0,0},{1,2,3,1,2},{2,4,6,2,4},{3,6,2,3,6},{4,1,5,4,1},{5,3,1,5,3},{6,5,4,6,5},
        {0,0,0,1,2},{1,2,3,2,4},{2,4,6,3,6},{3,6,2,4,1},{4,1,5,5,3},{5,3,1,6,5},{6,5,4,0,0},
        {0,1,0,4,2},{1,3,3,5,4},{2,5,6,6,6},{3,0,2,0,1},{4,2,5,1,3},{5,4,1,2,5},{6,6,4,3,0},
        {0,4,6,3,0},{1,6,2,4,2},{2,1,5,5,4},{3,3,1,6,6},{4,5,4,0,1},{5,0,0,1,3},{6,2,3,2,5},
        {0,5,6,0,2},{1,0,2,1,4},{2,2,5,0,6},{3,4,1,1,1},{4,6,4,2,3},{5,1,0,3,5},{6,3,3,4,0}
    };
    for (auto& a : c35_raw) C35.push_back(encode5(a));

    GadgetResult best_d{35,1,35,0,0,0,1225,{},{},{},{}}, best_sc{35,0,0,0,0,0,1225,{},{},{},{}};

    // Check several b=1 pairs on C35 (14+ pairs) to maximize d!
    auto pps_c35 = find_privs(C35);
    int tested = 0;
    for (const auto& pp : pps_c35) {
        if (pp.forb_sz != 1024) continue;
        scan_and_lns("C35-b1", C35, {pp.s}, {pp.q}, C35, best_d, best_sc, 600, 0);
        if (++tested >= 6) break;
    }
    // Full 3840 scan on best_d if found, plus S35's b=1 pair
    auto pps_s35 = find_privs(S35);
    scan_and_lns("S35-b1", S35, {pps_s35[0].s}, {pps_s35[0].q}, C35, best_d, best_sc, 3840, 0);

    // Check minimal-|F| b=2 and b=3 on C35 and S35 with Aut(C7^5) + LNS!
    for (const auto& [name, I] : std::vector<std::pair<const char*, std::vector<int>>>{{"C35", C35}, {"S35", S35}}) {
        auto pps = find_privs(I);
        std::vector<PrivPair> small;
        for (const auto& pp : pps) if (pp.forb_sz <= 1280) small.push_back(pp);
        int m = (int)small.size();
        int min_f2 = 99999;
        std::vector<int> bp0_2, bp1_2;
        for (int i = 0; i < m; ++i) {
            for (int j = i + 1; j < m; ++j) {
                if (small[i].s_idx == small[j].s_idx) continue;
                for (int ori = 0; ori < 2; ++ori) {
                    int p0b = ori ? small[j].q : small[j].s;
                    int p1b = ori ? small[j].s : small[j].q;
                    if (close5[small[i].s].test(p0b) || close5[small[i].q].test(p1b)) continue;
                    int fsz = 0;
                    for (int w = 0; w < W5; ++w) {
                        uint64_t n0 = close5[small[i].s].w[w] | close5[p0b].w[w];
                        uint64_t n1 = close5[small[i].q].w[w] | close5[p1b].w[w];
                        fsz += __builtin_popcountll(n0 & n1);
                    }
                    if (fsz < min_f2) { min_f2 = fsz; bp0_2 = {small[i].s, p0b}; bp1_2 = {small[i].q, p1b}; }
                }
            }
        }
        if (!bp0_2.empty()) {
            scan_and_lns(name, I, bp0_2, bp1_2, C35, best_d, best_sc, 3840, 5000);
            // Extend to b=3
            int min_f3 = 99999;
            std::vector<int> bp0_3, bp1_3;
            for (int k = 0; k < m; ++k) {
                if (small[k].s == bp0_2[0] || small[k].s == bp0_2[1] || small[k].s == bp1_2[1]) continue;
                for (int ori = 0; ori < 2; ++ori) {
                    int p0c = ori ? small[k].q : small[k].s;
                    int p1c = ori ? small[k].s : small[k].q;
                    if (close5[bp0_2[0]].test(p0c) || close5[bp0_2[1]].test(p0c)) continue;
                    if (close5[bp1_2[0]].test(p1c) || close5[bp1_2[1]].test(p1c)) continue;
                    int fsz = 0;
                    for (int w = 0; w < W5; ++w) {
                        uint64_t n0 = close5[bp0_2[0]].w[w] | close5[bp0_2[1]].w[w] | close5[p0c].w[w];
                        uint64_t n1 = close5[bp1_2[0]].w[w] | close5[bp1_2[1]].w[w] | close5[p1c].w[w];
                        fsz += __builtin_popcountll(n0 & n1);
                    }
                    if (fsz < min_f3) { min_f3 = fsz; bp0_3 = {bp0_2[0], bp0_2[1], p0c}; bp1_3 = {bp1_2[0], bp1_2[1], p1c}; }
                }
            }
            if (!bp0_3.empty()) scan_and_lns(name, I, bp0_3, bp1_3, C35, best_d, best_sc, 1000, 5000);
        }
    }

    auto save = [&](const char* path, const GadgetResult& g) {
        if (g.X.empty()) return;
        std::ofstream out(path);
        auto write_list = [&](const char* name, const std::vector<int>& lst) {
            out << "  \"" << name << "\": [";
            for (size_t i = 0; i < lst.size(); ++i) {
                auto c = coords5[lst[i]];
                out << "[" << c[0] << "," << c[1] << "," << c[2] << "," << c[3] << "," << c[4] << "]";
                if (i + 1 < lst.size()) out << ",";
            }
            out << "]";
        };
        out << "{\n  \"a\": " << g.a << ", \"b\": " << g.b << ", \"c\": " << g.c
            << ", \"d\": " << g.d << ", \"h\": " << g.h << ", \"v\": " << g.v << ",\n";
        write_list("I", g.I); out << ",\n";
        write_list("P0", g.P0); out << ",\n";
        write_list("P1", g.P1); out << ",\n";
        write_list("X", g.X); out << "\n}\n";
    };
    save("/mnt/nvme2tb/shannon_struct_scratch/compl/d5_gadget_max_d.json", best_d);
    save("/mnt/nvme2tb/shannon_struct_scratch/compl/d5_gadget_best_sc.json", best_sc);
    return 0;
}
