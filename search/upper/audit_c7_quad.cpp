// audit_c7_quad.cpp
// Structural taxonomy of all 1,016 Aut(C_7^3)-orbits of 33-sets, 1-swap adjacency graph,
// exact D_7-canonical profile classification for C_7^4 at N = 115, 114, 113, 112,
// and quantitative branching / neighborhood-coverage audit for Tier 1-4 refutation.
//
// Build: g++ -O3 -march=native -std=c++17 -Wall -Wextra search/upper/audit_c7_quad.cpp -o search/upper/audit_c7_quad
// Run:   ./search/upper/audit_c7_quad search/upper/c7_cube_33_orbits.txt

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
#include <queue>
#include <set>
#include <sstream>
#include <string>
#include <unordered_map>
#include <vector>

using u64 = uint64_t;
inline int popc(u64 x) { return __builtin_popcountll(x); }

struct Set343 {
    std::array<u64, 7> s{};
    bool operator==(const Set343& o) const { return s == o.s; }
    bool operator<(const Set343& o) const { return s < o.s; }
};

static const int PERMS6[6][3] = {
    {0, 1, 2}, {0, 2, 1}, {1, 0, 2}, {1, 2, 0}, {2, 0, 1}, {2, 1, 0}
};

static std::vector<int> CUBE_NBR[343];

static void init_cube_graph() {
    for (int v = 0; v < 343; ++v) {
        int a = v / 49, b = (v % 49) / 7, c = v % 7;
        for (int da = -1; da <= 1; ++da)
            for (int db = -1; db <= 1; ++db)
                for (int dc = -1; dc <= 1; ++dc) {
                    int u = ((a + da + 7) % 7) * 49 + ((b + db + 7) % 7) * 7 + ((c + dc + 7) % 7);
                    CUBE_NBR[v].push_back(u);
                }
    }
}

static Set343 canonicalize_343(const std::vector<int>& verts) {
    assert(verts.size() == 33);
    std::array<std::array<int, 3>, 33> pts;
    for (int i = 0; i < 33; ++i) {
        pts[i] = {verts[i] / 49, (verts[i] % 49) / 7, verts[i] % 7};
    }
    std::array<int, 33> best_idx;
    best_idx.fill(999);
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
                    cur_idx[i] = ((s0 * d[p0]) % 7) * 49 + ((s1 * d[p1]) % 7) * 7 + ((s2 * d[p2]) % 7);
                }
                std::sort(cur_idx.begin(), cur_idx.end());
                if (cur_idx < best_idx) best_idx = cur_idx;
            }
        }
    }
    Set343 canon{};
    for (int id : best_idx) canon.s[id / 49] |= (u64(1) << (id % 49));
    return canon;
}

static std::array<int, 7> canon_d7_profile(std::array<int, 7> p) {
    std::array<int, 7> best = p;
    for (int rev = 0; rev < 2; ++rev) {
        for (int sh = 0; sh < 7; ++sh) {
            std::array<int, 7> q;
            for (int i = 0; i < 7; ++i) {
                int idx = rev ? ((sh - i + 7) % 7) : ((sh + i) % 7);
                q[i] = p[idx];
            }
            if (q < best) best = q;
        }
    }
    return best;
}

int main(int argc, char** argv) {
    auto t0 = std::chrono::steady_clock::now();
    std::string orbit_path = (argc > 1) ? argv[1] : "search/upper/c7_cube_33_orbits.txt";
    init_cube_graph();

    // 1. Load all 1,016 canonical 33-set orbits
    struct Orbit {
        int id;
        int stab;
        int size;
        Set343 mask;
        std::vector<int> verts;
    };
    std::vector<Orbit> orbits;
    std::map<Set343, int> canon_to_id;
    {
        std::ifstream ifs(orbit_path);
        assert(ifs.good());
        std::string line;
        while (std::getline(ifs, line)) {
            if (line.empty() || line[0] == '#') continue;
            std::istringstream iss(line);
            Orbit ob;
            iss >> ob.id >> ob.stab >> ob.size;
            for (int z = 0; z < 7; ++z) {
                iss >> std::hex >> ob.mask.s[z] >> std::dec;
                u64 m = ob.mask.s[z];
                while (m) {
                    int v = __builtin_ctzll(m);
                    m &= m - 1;
                    ob.verts.push_back(z * 49 + v);
                }
            }
            assert(ob.verts.size() == 33);
            canon_to_id[ob.mask] = ob.id;
            orbits.push_back(std::move(ob));
        }
    }
    assert(orbits.size() == 1016);

    // 2. Exact C_7^4 slice-size profile enumeration for N = 115, 114, 113, 112
    std::cout << "=====================================================================\n";
    std::cout << "PART A: Exact D_7-Canonical Slice Profiles for C_7^4 (N=115..112)\n";
    std::cout << "=====================================================================\n";
    for (int N : {115, 114, 113, 112}) {
        std::set<std::array<int, 7>> profs;
        std::array<int, 7> cur{};
        auto dfs = [&](auto&& self, int i, int sum) -> void {
            if (i == 7) {
                if (sum == N && cur[6] + cur[0] <= 33) {
                    profs.insert(canon_d7_profile(cur));
                }
                return;
            }
            int lo = std::max(0, N - 3 * 33); // since any slice s_i >= N - 99!
            int hi = (i == 0) ? 33 : (33 - cur[i - 1]);
            for (int v = lo; v <= hi; ++v) {
                if (sum + v > N) break;
                int rem = 6 - i;
                int max_rem = (rem / 2) * 33 + (rem % 2) * (33 - v);
                if (sum + v + max_rem < N) continue;
                cur[i] = v;
                self(self, i + 1, sum + v);
            }
        };
        dfs(dfs, 0, 0);

        int min_b33 = 7, max_b33 = 0, zero_b33 = 0;
        std::map<int, int> b33_hist;
        for (const auto& p : profs) {
            int cnt33 = 0;
            for (int i = 0; i < 7; ++i) if (p[i] + p[(i + 1) % 7] == 33) cnt33++;
            min_b33 = std::min(min_b33, cnt33);
            max_b33 = std::max(max_b33, cnt33);
            if (cnt33 == 0) zero_b33++;
            b33_hist[cnt33]++;
        }
        std::cout << "  N = " << N << " (total deficit sum d_i = " << (7 * 33 - 2 * N)
                  << "): D_7-profiles = " << profs.size()
                  << ", #33-bands in [" << min_b33 << ", " << max_b33 << "]"
                  << ", zero-33-band profiles = " << zero_b33 << "\n";
        std::cout << "    #33-band histogram:";
        for (const auto& kv : b33_hist) std::cout << " " << kv.first << ":" << kv.second;
        std::cout << "\n";
        if (profs.size() <= 10) {
            for (const auto& p : profs) {
                int cnt33 = 0;
                for (int i = 0; i < 7; ++i) if (p[i] + p[(i + 1) % 7] == 33) cnt33++;
                std::cout << "      (";
                for (int i = 0; i < 7; ++i) std::cout << p[i] << (i < 6 ? "," : "");
                std::cout << ")  [#33-bands=" << cnt33 << "]\n";
            }
        }
    }

    // 3. Structural taxonomy & 1-swap overlap graph across all 1,016 orbits of C_7^3
    std::cout << "\n=====================================================================\n";
    std::cout << "PART B: Structural Taxonomy & 1-Swap Graph of ALL 1,016 33-Set Orbits\n";
    std::cout << "=====================================================================\n";
    std::map<std::array<int, 3>, int> band10_triple_hist;
    std::vector<std::set<int>> swap1_adj(1016);
    long long min_swap1_deg = 999999, max_swap1_deg = 0, sum_swap1_deg = 0;
    int isolated_orbits = 0;
    int min_uniq_dom = 999, max_uniq_dom = 0;
    double sum_uniq_dom = 0.0;

    for (const auto& ob : orbits) {
        // Count 10-bands along each of the 3 axes
        std::array<int, 3> b10_axes{0, 0, 0};
        for (int ax = 0; ax < 3; ++ax) {
            int scnt[7] = {0};
            for (int v : ob.verts) {
                int c = (ax == 0) ? (v / 49) : ((ax == 1) ? ((v % 49) / 7) : (v % 7));
                scnt[c]++;
            }
            for (int i = 0; i < 7; ++i)
                if (scnt[i] + scnt[(i + 1) % 7] == 10) b10_axes[ax]++;
        }
        std::sort(b10_axes.begin(), b10_axes.end());
        band10_triple_hist[b10_axes]++;

        // Domination multiplicity m(v) = |N[v] cap R_o| for every v in 0..342
        int dom[343] = {0};
        int uniq_owner[343];
        std::fill(std::begin(uniq_owner), std::end(uniq_owner), -1);
        for (int idx = 0; idx < 33; ++idx) {
            int w = ob.verts[idx];
            for (int u : CUBE_NBR[w]) {
                dom[u]++;
                uniq_owner[u] = idx;
            }
        }
        int uniq_dom_cnt = 0;
        long long swap1_cnt = 0;
        for (int u = 0; u < 343; ++u) {
            assert(dom[u] >= 1); // Every 33-set MUST be maximal!
            if (dom[u] == 1) {
                int owner_idx = uniq_owner[u];
                if (u != ob.verts[owner_idx]) {
                    uniq_dom_cnt++;
                    // Valid 1-swap: replace ob.verts[owner_idx] with u -> new 33-set!
                    swap1_cnt++;
                    std::vector<int> nxt = ob.verts;
                    nxt[owner_idx] = u;
                    auto c = canonicalize_343(nxt);
                    auto it = canon_to_id.find(c);
                    assert(it != canon_to_id.end()); // Independent completeness check!!
                    swap1_adj[ob.id].insert(it->second);
                }
            }
        }
        min_uniq_dom = std::min(min_uniq_dom, uniq_dom_cnt);
        max_uniq_dom = std::max(max_uniq_dom, uniq_dom_cnt);
        sum_uniq_dom += uniq_dom_cnt;
        min_swap1_deg = std::min(min_swap1_deg, swap1_cnt);
        max_swap1_deg = std::max(max_swap1_deg, swap1_cnt);
        sum_swap1_deg += swap1_cnt;
        if (swap1_cnt == 0) isolated_orbits++;
    }

    // Connected components of 1-swap quotient graph on the 1,016 orbits
    std::vector<int> vis(1016, 0);
    std::vector<int> comp_sizes;
    for (int i = 0; i < 1016; ++i) {
        if (vis[i]) continue;
        std::queue<int> q;
        q.push(i);
        vis[i] = 1;
        int sz = 0;
        while (!q.empty()) {
            int u = q.front(); q.pop();
            sz++;
            for (int v : swap1_adj[u]) {
                if (!vis[v]) { vis[v] = 1; q.push(v); }
            }
        }
        comp_sizes.push_back(sz);
    }
    std::sort(comp_sizes.begin(), comp_sizes.end(), std::greater<int>());

    std::cout << "  All 1,016 orbits verified maximal (dom[u] >= 1 for all 343 vertices).\n";
    std::cout << "  All 1-swap neighbors (" << sum_swap1_deg << " total moves across 1,016 reps) landed inside census (100% closed!).\n";
    std::cout << "  1-swap degree per 33-set: min=" << min_swap1_deg << ", max=" << max_swap1_deg
              << ", avg=" << std::fixed << std::setprecision(2) << (sum_swap1_deg / 1016.0)
              << ", rigid (0-swap) orbits=" << isolated_orbits << "\n";
    std::cout << "  1-swap quotient components on 1,016 orbits: count=" << comp_sizes.size()
              << ", largest sizes=";
    for (size_t i = 0; i < std::min<size_t>(comp_sizes.size(), 10); ++i)
        std::cout << comp_sizes[i] << (i + 1 < std::min<size_t>(comp_sizes.size(), 10) ? "," : "");
    std::cout << "\n";
    std::cout << "  Sorted (#10-bands along 3 axes) histogram across 1,016 orbits:\n";
    for (const auto& kv : band10_triple_hist) {
        std::cout << "    (" << kv.first[0] << "," << kv.first[1] << "," << kv.first[2]
                  << "): " << kv.second << " orbits\n";
    }

    // 4. Inspect the 5 high-symmetry orbits (|Stab| > 1)
    std::cout << "\n  High-symmetry orbits (|Stab| > 1):\n";
    for (const auto& ob : orbits) {
        if (ob.stab > 1) {
            std::cout << "    orbit " << ob.id << ": |Stab|=" << ob.stab
                      << ", |Orbit|=" << ob.size
                      << ", 1-swap_orbit_deg=" << swap1_adj[ob.id].size() << "\n";
        }
    }

    double dt = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
    std::cout << "\n[OK] Completed C_7^4 structural & 1-swap audit in " << std::fixed << std::setprecision(2) << dt << " s.\n";
    return 0;
}
