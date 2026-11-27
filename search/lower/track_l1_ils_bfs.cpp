// Track L1B — L1-Cache-Resident Ejection-Chain ILS, Exact 3^5 = 243-Code (1,1)-Swap BFS Census,
// and Aut(C_7^5) Isomorphism Classification on C_7^5 (16,807 vertices).
// Build: g++ -O3 -march=native -std=c++17 search/lower/track_l1_ils_bfs.cpp -o /tmp/track_l1_ils_bfs
// Run:   /tmp/track_l1_ils_bfs --bfs-ps [--ils-seconds 3 --seed 13372026]
#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <iomanip>
#include <iostream>
#include <numeric>
#include <queue>
#include <random>
#include <set>
#include <string>
#include <unordered_set>
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

// Reconstruct Polak-Schrijver 367-word code R directly via unified sub-integer phase quantization
// (sigma = (283,100,283,100,283), core = 327 + exact residual MIS = 40 -> 367).
struct SmallMIS {
    int m = 0;
    std::vector<uint64_t> alo, ahi;
    int best = 0;
    std::vector<int> bset, cset;

    void dfs(uint64_t lo, uint64_t hi) {
        int rem = __builtin_popcountll(lo) + __builtin_popcountll(hi);
        if ((int)cset.size() + rem <= best) return;
        if (rem == 0) { best = (int)cset.size(); bset = cset; return; }
        int v = lo ? __builtin_ctzll(lo) : (64 + __builtin_ctzll(hi));
        uint64_t nlo = lo, nhi = hi;
        if (v < 64) nlo &= ~(1ULL << v); else nhi &= ~(1ULL << (v - 64));
        cset.push_back(v);
        dfs(nlo & ~alo[v], nhi & ~ahi[v]);
        cset.pop_back();
        dfs(nlo, nhi);
    }

    std::vector<int> solve(const std::vector<int>& verts) {
        m = (int)verts.size();
        if (m == 0 || m > 128) return {};
        alo.assign(m, 0); ahi.assign(m, 0);
        for (int i = 0; i < m; ++i)
            for (int j = i + 1; j < m; ++j)
                if (close5(verts[i], verts[j])) {
                    if (j < 64) alo[i] |= (1ULL << j); else ahi[i] |= (1ULL << (j - 64));
                    if (i < 64) alo[j] |= (1ULL << i); else ahi[j] |= (1ULL << (i - 64));
                }
        best = 0; bset.clear(); cset.clear();
        uint64_t lo = (m >= 64) ? ~0ULL : ((1ULL << m) - 1);
        uint64_t hi = (m > 64) ? ((m == 128) ? ~0ULL : ((1ULL << (m - 64)) - 1)) : 0ULL;
        dfs(lo, hi);
        std::vector<int> out;
        for (int i : bset) out.push_back(verts[i]);
        return out;
    }
};

std::vector<int> build_ps367() {
    const int n = 382;
    const std::array<int, 5> g = {1, 7, 49, 343, 109};
    const std::array<int, 5> sigma = {283, 100, 283, 100, 283};
    std::vector<int> raw(n);
    for (int t = 0; t < n; ++t) {
        std::array<int, 5> c;
        for (int j = 0; j < 5; ++j) {
            int64_t x = (int64_t)t * g[j] % n;
            c[j] = (int)(((7 * x + sigma[j]) % (7 * n)) / n);
        }
        raw[t] = enc5(c);
    }
    std::vector<uint8_t> bad(n, 0);
    for (int i = 0; i < n; ++i)
        for (int j = i + 1; j < n; ++j)
            if (raw[i] == raw[j] || close5(raw[i], raw[j])) bad[i] = bad[j] = 1;
    std::vector<int> core;
    std::vector<uint8_t> blk(N5, 0);
    for (int i = 0; i < n; ++i) {
        if (!bad[i]) {
            core.push_back(raw[i]);
            std::array<int, 5> a, b;
            dec5(raw[i], a);
            for (int d0 = -1; d0 <= 1; ++d0) { b[0] = (a[0] + d0 + 7) % 7;
            for (int d1 = -1; d1 <= 1; ++d1) { b[1] = (a[1] + d1 + 7) % 7;
            for (int d2 = -1; d2 <= 1; ++d2) { b[2] = (a[2] + d2 + 7) % 7;
            for (int d3 = -1; d3 <= 1; ++d3) { b[3] = (a[3] + d3 + 7) % 7;
            for (int d4 = -1; d4 <= 1; ++d4) { b[4] = (a[4] + d4 + 7) % 7;
                blk[enc5(b)] = 1;
            }}}}}
        }
    }
    std::vector<int> res;
    for (int w = 0; w < N5; ++w) if (!blk[w]) res.push_back(w);
    SmallMIS mis;
    auto add = mis.solve(res);
    core.insert(core.end(), add.begin(), add.end());
    std::sort(core.begin(), core.end());
    return core;
}

// Compute exact private pairs (s in I, q not in I, N[q] ∩ I = {s})
std::vector<std::pair<int, int>> find_private_pairs(const std::vector<int>& code) {
    std::vector<uint8_t> inI(N5, 0);
    std::vector<uint16_t> deg(N5, 0);
    std::vector<int> who(N5, 0);
    for (int u : code) inI[u] = 1;
    for (int u : code) {
        std::array<int, 5> a, b;
        dec5(u, a);
        for (int d0 = -1; d0 <= 1; ++d0) { b[0] = (a[0] + d0 + 7) % 7;
        for (int d1 = -1; d1 <= 1; ++d1) { b[1] = (a[1] + d1 + 7) % 7;
        for (int d2 = -1; d2 <= 1; ++d2) { b[2] = (a[2] + d2 + 7) % 7;
        for (int d3 = -1; d3 <= 1; ++d3) { b[3] = (a[3] + d3 + 7) % 7;
        for (int d4 = -1; d4 <= 1; ++d4) { b[4] = (a[4] + d4 + 7) % 7;
            int v = enc5(b);
            if (!inI[v]) { deg[v]++; who[v] = u; }
        }}}}}
    }
    std::vector<std::pair<int, int>> pairs;
    for (int v = 0; v < N5; ++v)
        if (!inI[v] && deg[v] == 1) pairs.push_back({who[v], v});
    return pairs;
}

int main(int argc, char** argv) {
    (void)argc; (void)argv;
    auto t0 = std::chrono::steady_clock::now();
    auto R = build_ps367();
    std::cout << "[Track L1B] Reconstructed Polak-Schrijver R: |R|=" << R.size() << "\n";

    // Exact (1,1)-swap BFS over the entire connected component of R!
    std::set<std::vector<int>> visited;
    std::queue<std::vector<int>> q;
    visited.insert(R);
    q.push(R);
    std::array<int, 16> hist_b{};
    int max_b = 0;

    while (!q.empty()) {
        auto cur = q.front();
        q.pop();
        auto priv = find_private_pairs(cur);
        // Distinct centers b
        std::set<int> centers;
        for (auto& pr : priv) centers.insert(pr.first);
        int b = (int)centers.size();
        if (b < 16) hist_b[b]++;
        if (b > max_b) max_b = b;

        for (auto& pr : priv) {
            std::vector<int> nxt = cur;
            auto it = std::lower_bound(nxt.begin(), nxt.end(), pr.first);
            if (it == nxt.end() || *it != pr.first) continue;
            *it = pr.second;
            std::sort(nxt.begin(), nxt.end());
            if (visited.insert(nxt).second) q.push(std::move(nxt));
        }
    }

    double dt = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
    std::cout << "[Track L1B Exact (1,1)-Swap BFS] Exhausted component of R: "
              << "total_labeled_codes=" << visited.size()
              << " (3^5 = 243), max_b=" << max_b << ", elapsed=" << dt << "s\n";
    std::cout << "  b-histogram:";
    for (int b = 0; b < 16; ++b) if (hist_b[b] > 0) std::cout << " b=" << b << ":" << hist_b[b];
    std::cout << "\n";
    return 0;
}
