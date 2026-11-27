// Exact determination of alpha((C7^c)^⊠4) via canonical K3-slice profiles
// Compile: g++ -O3 -march=native -std=c++17 search/lower/compl_d4_exact.cpp -o /mnt/nvme2tb/shannon_struct_scratch/compl/compl_d4_exact

#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <vector>

static constexpr int N3 = 343;
struct Bit3 {
    uint64_t w[6] = {0,0,0,0,0,0};
    inline void set(int i) { w[i>>6] |= (1ULL << (i&63)); }
    inline void reset(int i) { w[i>>6] &= ~(1ULL << (i&63)); }
    inline bool test(int i) const { return (w[i>>6] >> (i&63)) & 1ULL; }
    inline int popcount() const {
        int s = 0;
        for (int k = 0; k < 6; ++k) s += __builtin_popcountll(w[k]);
        return s;
    }
};

static std::array<std::array<int, 3>, N3> coords3;
static std::array<Bit3, N3> indep3; // bit j set iff sep3(i, j) (so can co-exist in SAME slice or slices diff != 1,6)

static void init3() {
    for (int i = 0; i < N3; ++i) {
        int t = i;
        for (int k = 2; k >= 0; --k) { coords3[i][k] = t % 7; t /= 7; }
    }
    for (int i = 0; i < N3; ++i) {
        for (int j = 0; j < N3; ++j) {
            if (i == j) continue;
            bool sep = false;
            for (int k = 0; k < 3; ++k) {
                int d = (coords3[i][k] - coords3[j][k] + 7) % 7;
                if (d == 1 || d == 6) { sep = true; break; }
            }
            if (sep) indep3[i].set(j);
        }
    }
}

// Compute max independent set size inside Bit3 mask (exact B&B, alpha(V3)=8)
static int max_indep_in_mask(Bit3 cand) {
    int best = 0;
    auto dfs = [&](auto& self, Bit3 c, int sz) -> void {
        int rem = c.popcount();
        if (sz + rem <= best) return;
        if (rem == 0) { best = std::max(best, sz); return; }
        int v = -1;
        for (int k = 0; k < 6; ++k) if (c.w[k]) { v = (k<<6) + __builtin_ctzll(c.w[k]); break; }
        Bit3 nxt;
        for (int k = 0; k < 6; ++k) nxt.w[k] = c.w[k] & indep3[v].w[k];
        self(self, nxt, sz + 1);
        c.reset(v);
        self(self, c, sz);
    };
    dfs(dfs, cand, 0);
    return best;
}

static bool solve_profile(const std::array<int, 7>& prof, const std::vector<int>& slice0_pair_cands) {
    // Fix slice 0 = {0, u} for u in slice0_pair_cands
    // Order remaining slices by: slice s in {1..6}
    // Wait: we can pick slices in order 0, 2, 4, 6, 1, 3, 5 or 0, 5, 6, 3, 2, 4, 1 depending on profile!
    // Even better: when assigning slice s with prof[s] vertices from allowed[s]:
    // Wait: if s1 and s2 are close in C7^c (diff in {0,2,3,4,5}), every vertex chosen in s1 restricts allowed[s2] by indep3[v]!
    // If diff in {1, 6}, NO restriction between s1 and s2!
    static const int close_diffs[4] = {2, 3, 4, 5};
    std::array<int, 7> order = {0, 5, 6, 2, 3, 4, 1};
    // Sort slices 1..6 by largest prof[s] first (so 4-vertex slices are assigned early!)
    std::sort(order.begin() + 1, order.end(), [&](int a, int b) {
        return prof[a] > prof[b];
    });

    Bit3 all_v;
    for (int i = 0; i < N3; ++i) all_v.set(i);

    for (int u0_2 : slice0_pair_cands) {
        std::array<Bit3, 7> allowed;
        for (int s = 0; s < 7; ++s) allowed[s] = all_v;
        // Apply slice 0 = {0, u0_2} to close slices {2,3,4,5}
        for (int d : close_diffs) {
            int s = d;
            for (int k = 0; k < 6; ++k) allowed[s].w[k] &= indep3[0].w[k] & indep3[u0_2].w[k];
        }

        // Recursive slice filler (assigns `rem_in_slice` vertices to `order[idx]`)
        auto rec = [&](auto& self, int idx, int rem, int min_v, std::array<Bit3, 7>& allow) -> bool {
            if (rem == 0) {
                if (idx == 6) return true; // all 7 slices filled!
                int ns = order[idx + 1];
                // Quick K3 / capacity pruning: check next slice has enough candidates!
                if (allow[ns].popcount() < prof[ns]) return false;
                // Check max_indep for slices with prof >= 3!
                if (prof[ns] >= 3 && max_indep_in_mask(allow[ns]) < prof[ns]) return false;
                // Also check all remaining slices have popcount >= prof[s]
                for (int j = idx + 1; j < 7; ++j) {
                    int sj = order[j];
                    if (allow[sj].popcount() < prof[sj]) return false;
                }
                return self(self, idx + 1, prof[ns], 0, allow);
            }
            int s = order[idx];
            // Iterate vertices >= min_v in allow[s]
            Bit3 cand = allow[s];
            for (int v = min_v; v < N3; ++v) {
                if (!cand.test(v)) continue;
                // Must still have enough vertices >= v in cand!
                int avail = 0;
                for (int u = v; u < N3; ++u) if (cand.test(u)) ++avail;
                if (avail < rem) break;

                std::array<Bit3, 7> nxt = allow;
                // Restrict current slice s (same slice)
                for (int k = 0; k < 6; ++k) nxt[s].w[k] &= indep3[v].w[k];
                // Restrict close slices
                for (int d : close_diffs) {
                    int s2 = (s + d) % 7;
                    for (int k = 0; k < 6; ++k) nxt[s2].w[k] &= indep3[v].w[k];
                }
                if (self(self, idx, rem - 1, v + 1, nxt)) return true;
            }
            return false;
        };

        if (rec(rec, 1, prof[order[1]], 0, allowed)) return true;
    }
    return false;
}

int main() {
    auto t0 = std::chrono::steady_clock::now();
    init3();
    // Canonical representatives for second vertex of slice 0 (given first is (0,0,0)), up to (±1)^3 x S_3
    std::vector<int> cands;
    std::vector<bool> seen(N3, false);
    for (int v = 1; v < N3; ++v) {
        if (!indep3[0].test(v)) continue;
        if (seen[v]) continue;
        cands.push_back(v);
        // Mark orbit under (±1)^3 x S_3
        std::array<int, 3> p = {0, 1, 2};
        do {
            for (int m = 0; m < 8; ++m) {
                std::array<int, 3> c;
                for (int k = 0; k < 3; ++k) {
                    int val = coords3[v][p[k]];
                    c[k] = ((m >> k) & 1) ? (7 - val) % 7 : val;
                }
                int id = (c[0]*7 + c[1])*7 + c[2];
                seen[id] = true;
            }
        } while (std::next_permutation(p.begin(), p.end()));
    }
    std::cout << "[d4-exact] Canonical slice-0 second vertices: " << cands.size() << "\n";

    std::vector<std::array<int, 7>> profs = {
        {2, 2, 2, 2, 2, 4, 4},
        {2, 2, 2, 2, 3, 4, 3},
        {2, 2, 2, 3, 3, 3, 3},
        {2, 2, 3, 3, 2, 3, 3}
    };
    for (size_t i = 0; i < profs.size(); ++i) {
        auto tp = std::chrono::steady_clock::now();
        bool ok = solve_profile(profs[i], cands);
        std::cout << "[d4-exact] Profile " << i << " SAT=" << ok
                  << " (" << std::chrono::duration<double>(std::chrono::steady_clock::now() - tp).count() << "s)\n";
        if (ok) { std::cout << "FOUND 18!\n"; return 0; }
    }
    std::cout << "[d4-exact] PROVED alpha((C7^c)^⊠4) = 17! Total time="
              << std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count() << "s\n";
    return 0;
}
