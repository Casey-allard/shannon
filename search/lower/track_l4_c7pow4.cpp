// Track L4 — C_7^4 >= 109 Bit-Parallel ILS + Exact (1,2)-Swap & Plateau-Kick Probe.
// Build: g++ -O3 -march=native -std=c++17 search/lower/track_l4_c7pow4.cpp -o /tmp/track_l4_c7pow4
// Run:   /tmp/track_l4_c7pow4 --seconds 5 --seed 2026112604
#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <random>
#include <string>
#include <vector>

static constexpr int N4 = 2401;
static constexpr int WORDS = 38; // 38 * 64 = 2432 >= 2401

inline int enc4(int a, int b, int c, int d) { return ((a * 7 + b) * 7 + c) * 7 + d; }
inline void dec4(int id, int c[4]) {
    for (int i = 3; i >= 0; --i) { c[i] = id % 7; id /= 7; }
}

struct GraphC7Pow4 {
    std::vector<std::array<uint64_t, WORDS>> adj_bits;
    std::vector<std::vector<int>> adj;

    GraphC7Pow4() : adj_bits(N4), adj(N4) {
        for (int u = 0; u < N4; ++u) adj_bits[u].fill(0);
        int a[4], b[4];
        for (int u = 0; u < N4; ++u) {
            dec4(u, a);
            for (int d0 = -1; d0 <= 1; ++d0) { b[0] = (a[0] + d0 + 7) % 7;
            for (int d1 = -1; d1 <= 1; ++d1) { b[1] = (a[1] + d1 + 7) % 7;
            for (int d2 = -1; d2 <= 1; ++d2) { b[2] = (a[2] + d2 + 7) % 7;
            for (int d3 = -1; d3 <= 1; ++d3) { b[3] = (a[3] + d3 + 7) % 7;
                int v = enc4(b[0], b[1], b[2], b[3]);
                if (v != u) {
                    adj[u].push_back(v);
                    adj_bits[u][v >> 6] |= (1ULL << (v & 63));
                }
            }}}}
        }
    }
};

struct FastIS4 {
    const GraphC7Pow4& G;
    std::array<uint8_t, N4> inS{};
    std::array<int, N4> degS{};
    std::array<int, N4> xorS{};
    std::vector<int> S;

    explicit FastIS4(const GraphC7Pow4& g) : G(g) {}

    void clear() {
        inS.fill(0); degS.fill(0); xorS.fill(0); S.clear();
    }

    void add(int u) {
        inS[u] = 1;
        S.push_back(u);
        for (int v : G.adj[u]) { degS[v]++; xorS[v] ^= u; }
    }

    void rem(int u) {
        inS[u] = 0;
        auto it = std::find(S.begin(), S.end(), u);
        if (it != S.end()) { *it = S.back(); S.pop_back(); }
        for (int v : G.adj[u]) { degS[v]--; xorS[v] ^= u; }
    }

    void greedy_fill(std::mt19937_64& rng) {
        std::vector<int> free_v;
        for (int v = 0; v < N4; ++v) if (!inS[v] && degS[v] == 0) free_v.push_back(v);
        while (!free_v.empty()) {
            std::shuffle(free_v.begin(), free_v.end(), rng);
            int pick = -1;
            for (int v : free_v) {
                if (!inS[v] && degS[v] == 0) { pick = v; break; }
            }
            if (pick == -1) break;
            add(pick);
            free_v.erase(std::remove_if(free_v.begin(), free_v.end(),
                         [&](int v){ return inS[v] || degS[v] != 0; }), free_v.end());
        }
    }

    // Exact (1,2)-swap: check every u in S for two non-adjacent 1-tight neighbors
    bool try_12_swap() {
        std::vector<std::vector<int>> tight(N4);
        for (int v = 0; v < N4; ++v)
            if (!inS[v] && degS[v] == 1) tight[xorS[v]].push_back(v);
        for (int u : S) {
            const auto& tv = tight[u];
            for (size_t i = 0; i < tv.size(); ++i) {
                int a = tv[i];
                for (size_t j = i + 1; j < tv.size(); ++j) {
                    int b = tv[j];
                    if (!((G.adj_bits[a][b >> 6] >> (b & 63)) & 1ULL)) {
                        rem(u); add(a); add(b);
                        return true;
                    }
                }
            }
        }
        return false;
    }

    bool verify() const {
        for (size_t i = 0; i < S.size(); ++i)
            for (size_t j = i + 1; j < S.size(); ++j)
                if (S[i] == S[j] || ((G.adj_bits[S[i]][S[j] >> 6] >> (S[j] & 63)) & 1ULL))
                    return false;
        return true;
    }
};

int main(int argc, char** argv) {
    double seconds = 2.0;
    uint64_t seed = 2026112604ULL;
    for (int i = 1; i + 1 < argc; i += 2) {
        std::string k = argv[i];
        if (k == "--seconds") seconds = std::stod(argv[i + 1]);
        else if (k == "--seed") seed = std::stoull(argv[i + 1]);
    }
    GraphC7Pow4 G;
    FastIS4 is(G);
    std::mt19937_64 rng(seed);
    auto t0 = std::chrono::steady_clock::now();

    int best_sz = 0;
    uint64_t iters = 0, swaps12 = 0, restarts = 0;
    while (std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count() < seconds) {
        is.clear();
        is.greedy_fill(rng);
        restarts++;
        for (int step = 0; step < 300; ++step) {
            iters++;
            while (is.try_12_swap()) { swaps12++; is.greedy_fill(rng); }
            if ((int)is.S.size() > best_sz) {
                if (!is.verify()) { std::cerr << "Conflict bug!\n"; return 1; }
                best_sz = (int)is.S.size();
            }
            // Random plateau / slice kick
            int k = 4 + (int)(rng() % 8);
            for (int r = 0; r < k && !is.S.empty(); ++r) {
                int u = is.S[rng() % is.S.size()];
                is.rem(u);
            }
            is.greedy_fill(rng);
        }
    }
    double dt = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
    std::cout << "[Track L4 Probe] elapsed=" << dt << "s restarts=" << restarts
              << " iters=" << iters << " swaps12=" << swaps12
              << " best_fresh_size=" << best_sz << " (verified 0 conflicts; heuristic only)\n";
    return 0;
}
