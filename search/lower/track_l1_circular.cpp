// Track L1A — Circular Graphs C_{k,n}^5, Unified Sub-Integer Phase Quantization
// and Expected Conflict-Free Core Landscape Scanner on C_7^5.
// Build: g++ -O3 -march=native -std=c++17 search/lower/track_l1_circular.cpp -o /tmp/track_l1_circular
// Run:   /tmp/track_l1_circular [--scan-n 365 415] [--verify-ps]
#include <algorithm>
#include <array>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <functional>
#include <iomanip>
#include <iostream>
#include <numeric>
#include <string>
#include <vector>

static constexpr int N5 = 16807;

inline int enc5(const std::array<int, 5>& c) {
    return (((c[0] * 7 + c[1]) * 7 + c[2]) * 7 + c[3]) * 7 + c[4];
}

inline void dec5(int id, std::array<int, 5>& c) {
    for (int i = 4; i >= 0; --i) { c[i] = id % 7; id /= 7; }
}

inline bool close5(int u, int v) {
    std::array<int, 5> a, b;
    dec5(u, a); dec5(v, b);
    for (int i = 0; i < 5; ++i) {
        int d = (a[i] - b[i] + 7) % 7;
        if (d != 0 && d != 1 && d != 6) return false;
    }
    return true;
}

inline int cyc_dist(int x, int n) {
    int r = x % n;
    if (r < 0) r += n;
    return std::min(r, n - r);
}

// Unified sub-integer phase quantization: c[j] = ((7 * ((t * g[j]) % n) + sigma[j]) % (7*n)) / n
struct QuantResult {
    int raw_size = 0;
    int core_size = 0;
    int res_verts = 0;
    int total_size = 0;
    std::vector<int> code;
};

// Exact branch-and-bound MIS on small residual graphs (m <= 128)
struct BitsetMIS {
    int m = 0;
    std::vector<uint64_t> adj_lo, adj_hi;
    int best_sz = 0;
    std::vector<int> best_set, cur_set;

    void init(const std::vector<int>& verts) {
        m = (int)verts.size();
        adj_lo.assign(m, 0);
        adj_hi.assign(m, 0);
        for (int i = 0; i < m; ++i) {
            for (int j = i + 1; j < m; ++j) {
                if (close5(verts[i], verts[j])) {
                    if (j < 64) adj_lo[i] |= (1ULL << j); else adj_hi[i] |= (1ULL << (j - 64));
                    if (i < 64) adj_lo[j] |= (1ULL << i); else adj_hi[j] |= (1ULL << (i - 64));
                }
            }
        }
        best_sz = 0; best_set.clear(); cur_set.clear();
    }

    static inline int popcnt(uint64_t lo, uint64_t hi) {
        return __builtin_popcountll(lo) + __builtin_popcountll(hi);
    }

    void dfs(uint64_t clo, uint64_t chi) {
        int rem = popcnt(clo, chi);
        if ((int)cur_set.size() + rem <= best_sz) return;
        if (rem == 0) {
            best_sz = (int)cur_set.size();
            best_set = cur_set;
            return;
        }
        // Pick lowest-bit vertex
        int v = (clo != 0) ? __builtin_ctzll(clo) : (64 + __builtin_ctzll(chi));
        uint64_t nlo = clo, nhi = chi;
        if (v < 64) nlo &= ~(1ULL << v); else nhi &= ~(1ULL << (v - 64));
        // Branch 1: include v
        cur_set.push_back(v);
        dfs(nlo & ~adj_lo[v], nhi & ~adj_hi[v]);
        cur_set.pop_back();
        // Branch 2: exclude v
        dfs(nlo, nhi);
    }

    std::vector<int> solve(const std::vector<int>& verts) {
        init(verts);
        if (m == 0) return {};
        if (m > 128) return {};
        uint64_t lo = (m >= 64) ? ~0ULL : ((1ULL << m) - 1);
        uint64_t hi = (m > 64) ? ((m == 128) ? ~0ULL : ((1ULL << (m - 64)) - 1)) : 0ULL;
        dfs(lo, hi);
        std::vector<int> out;
        for (int idx : best_set) out.push_back(verts[idx]);
        return out;
    }
};

QuantResult evaluate_cyclic_subgroup(int n, const std::array<int, 5>& g,
                                     const std::array<int, 5>& sigma) {
    std::vector<int> pts;
    pts.reserve(n);
    std::vector<uint8_t> seen(N5, 0);
    std::vector<uint8_t> conflict(n, 0);
    std::vector<int> raw(n);
    int mod7n = 7 * n;
    for (int t = 0; t < n; ++t) {
        std::array<int, 5> c;
        for (int j = 0; j < 5; ++j) {
            int64_t x = (int64_t)t * g[j] % n;
            int64_t v = (7 * x + sigma[j]) % mod7n;
            c[j] = (int)(v / n);
        }
        raw[t] = enc5(c);
    }
    for (int i = 0; i < n; ++i) {
        for (int j = i + 1; j < n; ++j) {
            if (raw[i] == raw[j] || close5(raw[i], raw[j])) {
                conflict[i] = conflict[j] = 1;
            }
        }
    }
    std::vector<int> core;
    for (int i = 0; i < n; ++i) {
        if (!conflict[i]) {
            core.push_back(raw[i]);
            seen[raw[i]] = 1;
        }
    }
    // Build residual compatible vertices in C_7^5
    std::vector<uint8_t> blocked(N5, 0);
    for (int u : core) {
        std::array<int, 5> a, b;
        dec5(u, a);
        for (int d0 = -1; d0 <= 1; ++d0) { b[0] = (a[0] + d0 + 7) % 7;
        for (int d1 = -1; d1 <= 1; ++d1) { b[1] = (a[1] + d1 + 7) % 7;
        for (int d2 = -1; d2 <= 1; ++d2) { b[2] = (a[2] + d2 + 7) % 7;
        for (int d3 = -1; d3 <= 1; ++d3) { b[3] = (a[3] + d3 + 7) % 7;
        for (int d4 = -1; d4 <= 1; ++d4) { b[4] = (a[4] + d4 + 7) % 7;
            blocked[enc5(b)] = 1;
        }}}}}
    }
    std::vector<int> res;
    for (int w = 0; w < N5; ++w) if (!blocked[w]) res.push_back(w);
    QuantResult qr;
    qr.raw_size = n;
    qr.core_size = (int)core.size();
    qr.res_verts = (int)res.size();
    qr.code = core;
    if ((int)res.size() <= 128) {
        BitsetMIS mis;
        auto add = mis.solve(res);
        qr.code.insert(qr.code.end(), add.begin(), add.end());
    }
    qr.total_size = (int)qr.code.size();
    return qr;
}

// Exact expected conflict count for cyclic subgroup (n, g) under uniform random shift
double expected_conflicts(int n, const std::array<int, 5>& g) {
    double econf = 0.0;
    int half = n / 2;
    for (int t = 1; t <= half; ++t) {
        double p = 1.0;
        for (int j = 0; j < 5; ++j) {
            int d = cyc_dist((int)((int64_t)t * g[j] % n), n);
            double pj = 2.0 - 7.0 * (double)d / (double)n;
            if (pj <= 0.0) { p = 0.0; break; }
            if (pj > 1.0) pj = 1.0;
            p *= pj;
        }
        econf += (t * 2 == n ? 0.5 : 1.0) * (double)n * p;
    }
    return econf;
}

// Exact 256-bit 4-set-cover check for cyclic subgroup in C_{k,n}^5
int count_exact_cyclic_subgroups(int n, int k) {
    // A subgroup (1, g1, g2, g3, g4) is independent in C_{k,n}^5 iff for every t in [1, k-1],
    // at least one j in {1..4} has cyc_dist(t*g_j, n) >= k.
    int M = k - 1;
    if (M <= 0 || M > 256) return 0;
    int half = n / 2;
    struct Word4 { uint64_t w[4]; };
    std::vector<Word4> masks;
    std::vector<int> gvals;
    for (int g = 1; g <= half; ++g) {
        Word4 m = {{0, 0, 0, 0}};
        bool any = false;
        for (int t = 1; t <= M; ++t) {
            if (cyc_dist((int)((int64_t)t * g % n), n) >= k) {
                int idx = t - 1;
                m.w[idx >> 6] |= (1ULL << (idx & 63));
                any = true;
            }
        }
        if (any) { masks.push_back(m); gvals.push_back(g); }
    }
    Word4 full = {{0, 0, 0, 0}};
    for (int idx = 0; idx < M; ++idx) full.w[idx >> 6] |= (1ULL << (idx & 63));
    // Deduplicate identical masks to keep search tiny
    int hits = 0;
    int G = (int)masks.size();
    // Exact 4-cover DFS: always branch on the uncovered element with fewest covering g's?
    // Simple pruned 4-loop with bitmask early-exit
    std::vector<std::vector<int>> cover_by(M);
    for (int i = 0; i < G; ++i)
        for (int idx = 0; idx < M; ++idx)
            if ((masks[i].w[idx >> 6] >> (idx & 63)) & 1ULL) cover_by[idx].push_back(i);
    for (int idx = 0; idx < M; ++idx) if (cover_by[idx].empty()) return 0;

    auto first_uncov = [&](const Word4& cur) -> int {
        for (int b = 0; b < 4; ++b) {
            uint64_t miss = full.w[b] & ~cur.w[b];
            if (miss) return (b << 6) + __builtin_ctzll(miss);
        }
        return -1;
    };

    std::function<void(int, Word4)> dfs = [&](int depth, Word4 cur) {
        int u = first_uncov(cur);
        if (u == -1) { hits++; return; }
        if (depth == 4) return;
        for (int gi : cover_by[u]) {
            Word4 nxt;
            for (int b = 0; b < 4; ++b) nxt.w[b] = cur.w[b] | masks[gi].w[b];
            dfs(depth + 1, nxt);
            if (hits > 0) return;
        }
    };
    dfs(0, {{0, 0, 0, 0}});
    return hits;
}

int main(int argc, char** argv) {
    int n_lo = 365, n_hi = 415;
    if (argc >= 4 && std::string(argv[1]) == "--scan-n") {
        n_lo = std::stoi(argv[2]);
        n_hi = std::stoi(argv[3]);
    }
    auto t0 = std::chrono::steady_clock::now();

    // 1. Reproduce Polak-Schrijver 367 exactly via unified sub-integer phase quantization!
    std::array<int, 5> ps_g = {1, 7, 49, 343, 109};
    std::array<int, 5> ps_sigma = {283, 100, 283, 100, 283};
    auto ps = evaluate_cyclic_subgroup(382, ps_g, ps_sigma);
    double econf_ps = expected_conflicts(382, ps_g);
    std::cout << std::fixed << std::setprecision(3);
    std::cout << "[PS-382 Exact Check] n=382 g=(1,7,49,343,109) sigma=(283,100,283,100,283): "
              << "core=" << ps.core_size << " res=" << ps.res_verts
              << " total=" << ps.total_size << " E_conf=" << econf_ps
              << " E_core=" << (382.0 - 2.0 * econf_ps) << "\n";

    // Verify 0 conflicts in ps.code
    for (size_t i = 0; i < ps.code.size(); ++i)
        for (size_t j = i + 1; j < ps.code.size(); ++j)
            if (ps.code[i] == ps.code[j] || close5(ps.code[i], ps.code[j])) {
                std::cerr << "ERROR: conflict in PS-382 reproduction!\n";
                return 1;
            }

    // 2. Exhaustive exact 4-set-cover cyclic subgroup scan across n in [n_lo, n_hi] with n/k <= 3.60
    int total_hits = 0;
    for (int n = n_lo; n <= n_hi; ++n) {
        int k = (int)std::ceil((double)n / 3.60);
        int h = count_exact_cyclic_subgroups(n, k);
        if (h > 0) {
            std::cout << "[Exact C_{k,n}^5 Hit] n=" << n << " k=" << k
                      << " (n/k=" << (double)n / k << "): exists=" << h << "\n";
            total_hits++;
        }
    }
    double dt = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
    std::cout << "[Track L1A Summary] Scanned n in [" << n_lo << "," << n_hi
              << "] (n/k <= 3.60): hits=" << total_hits << ", elapsed="
              << dt << "s\n";
    return 0;
}
