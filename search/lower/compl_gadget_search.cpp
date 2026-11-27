// Stage 3 v2: Fast (1,1)-swap walk + ILS/LNS on V5 \ F for ValidTuple & PartGadget in d=5
// Compile: g++ -O3 -march=native -std=c++17 search/lower/compl_gadget_search.cpp -o /mnt/nvme2tb/shannon_struct_scratch/compl/compl_gadget_search

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

struct PrivPair {
    int s_idx, s, q, forb_sz;
};

static std::vector<PrivPair> find_private_pairs(const std::vector<int>& I) {
    std::vector<int> tight(N5, 0), uniq_s(N5, -1);
    for (int si = 0; si < (int)I.size(); ++si) {
        int u = I[si];
        for (int w = 0; w < W5; ++w) {
            uint64_t b = close5[u].w[w];
            while (b) {
                int bit = __builtin_ctzll(b); b &= b - 1;
                int v = (w << 6) + bit;
                ++tight[v]; uniq_s[v] = si;
            }
        }
    }
    std::vector<PrivPair> res;
    for (int v = 0; v < N5; ++v) {
        if (tight[v] == 1) {
            int si = uniq_s[v];
            int s = I[si];
            if (v != s) {
                int fsz = 0;
                for (int w = 0; w < W5; ++w) fsz += __builtin_popcountll(close5[s].w[w] & close5[v].w[w]);
                res.push_back({si, s, v, fsz});
            }
        }
    }
    std::sort(res.begin(), res.end(), [](const PrivPair& a, const PrivPair& b) {
        return a.forb_sz < b.forb_sz;
    });
    return res;
}

static bool verify_indep5(const std::vector<int>& S) {
    for (size_t i = 0; i < S.size(); ++i)
        for (size_t j = i + 1; j < S.size(); ++j)
            if (close5[S[i]].test(S[j])) return false;
    return true;
}

// Search for maximum independent set X inside V5 \ F using ILS + LNS
static std::vector<int> search_indep_avoiding_F(
        const Bitset5& forb, const std::vector<int>& base_S35, int target_c, int time_ms) {
    auto t0 = std::chrono::steady_clock::now();
    std::mt19937_64 rng(998877ULL);
    std::vector<int> allowed;
    std::vector<bool> is_forb(N5, false);
    for (int v = 0; v < N5; ++v) {
        if (forb.test(v)) is_forb[v] = true;
        else allowed.push_back(v);
    }

    // Seed with random Aut(C7^5) transforms of base_S35 filtered by !is_forb
    std::vector<int> best_X;
    std::vector<int> tight(N5, 0);

    // Quick find best shifted/permuted seed
    for (int tr = 0; tr < 300; ++tr) {
        std::array<int, 5> perm = {0, 1, 2, 3, 4};
        std::shuffle(perm.begin(), perm.end(), rng);
        std::array<int, 5> sgn, sh;
        for (int k = 0; k < 5; ++k) { sgn[k] = (rng() & 1) ? 6 : 1; sh[k] = rng() % 7; }
        std::vector<int> cand;
        for (int u : base_S35) {
            std::array<int, 5> c;
            for (int k = 0; k < 5; ++k) c[k] = (coords5[u][perm[k]] * sgn[k] + sh[k]) % 7;
            int v = encode5(c);
            if (!is_forb[v]) cand.push_back(v);
        }
        if (cand.size() > best_X.size()) best_X = cand;
        if ((int)best_X.size() >= target_c) return best_X;
    }

    // ILS starting from best_X (size ~34!) inside allowed!
    while (std::chrono::duration<double, std::milli>(std::chrono::steady_clock::now() - t0).count() < time_ms) {
        std::vector<int> S = best_X;
        std::fill(tight.begin(), tight.end(), 0);
        for (int u : S) {
            for (int w = 0; w < W5; ++w) {
                uint64_t b = close5[u].w[w];
                while (b) { int bit = __builtin_ctzll(b); b &= b - 1; ++tight[(w << 6) + bit]; }
            }
        }
        for (int step = 0; step < 2500; ++step) {
            // Greedy add any free allowed vertex
            for (int v : allowed) {
                if (tight[v] == 0) {
                    S.push_back(v);
                    for (int w = 0; w < W5; ++w) {
                        uint64_t b = close5[v].w[w];
                        while (b) { int bit = __builtin_ctzll(b); b &= b - 1; ++tight[(w << 6) + bit]; }
                    }
                }
            }
            if (S.size() > best_X.size() && verify_indep5(S)) {
                best_X = S;
                if ((int)best_X.size() >= target_c) return best_X;
            }
            // Pick a 1-tight allowed vertex or kick 2 vertices
            std::vector<int> c1;
            for (int v : allowed) if (tight[v] == 1) c1.push_back(v);
            if (!c1.empty() && (step % 15 != 0)) {
                int v = c1[rng() % c1.size()];
                int bi = -1;
                for (int i = 0; i < (int)S.size(); ++i) if (close5[S[i]].test(v)) { bi = i; break; }
                int rem = S[bi];
                S[bi] = v;
                for (int w = 0; w < W5; ++w) {
                    uint64_t b_rem = close5[rem].w[w], b_v = close5[v].w[w];
                    uint64_t diff = b_rem ^ b_v;
                    while (diff) {
                        int bit = __builtin_ctzll(diff); diff &= diff - 1;
                        int idx = (w << 6) + bit;
                        tight[idx] += ((b_v >> bit) & 1ULL) ? 1 : -1;
                    }
                }
            } else {
                // Destroy 2..4 vertices and re-fill randomly
                int drop_k = 2 + (rng() % 3);
                for (int r = 0; r < drop_k && !S.empty(); ++r) {
                    int bi = rng() % S.size();
                    int rem = S[bi];
                    S[bi] = S.back(); S.pop_back();
                    for (int w = 0; w < W5; ++w) {
                        uint64_t b = close5[rem].w[w];
                        while (b) { int bit = __builtin_ctzll(b); b &= b - 1; --tight[(w << 6) + bit]; }
                    }
                }
                // Shuffle scan a bit
                for (int tries = 0; tries < 400; ++tries) {
                    int v = allowed[rng() % allowed.size()];
                    if (tight[v] == 0) {
                        S.push_back(v);
                        for (int w = 0; w < W5; ++w) {
                            uint64_t b = close5[v].w[w];
                            while (b) { int bit = __builtin_ctzll(b); b &= b - 1; ++tight[(w << 6) + bit]; }
                        }
                    }
                }
            }
        }
    }
    return best_X;
}

int main() {
    auto t0 = std::chrono::steady_clock::now();
    init5();

    std::vector<int> S35;
    std::array<int, 5> g5 = {1, 2, 3, 1, 2};
    std::vector<std::array<int, 5>> seeds5 = {{0,0,0,0,0},{0,0,0,1,1},{0,0,1,4,3},{0,2,0,2,1},{0,2,1,1,4}};
    for (const auto& sd : seeds5)
        for (int t = 0; t < 7; ++t)
            S35.push_back(encode5({(sd[0]+t*g5[0])%7, (sd[1]+t*g5[1])%7, (sd[2]+t*g5[2])%7, (sd[3]+t*g5[3])%7, (sd[4]+t*g5[4])%7}));

    // Phase 1: Walk 10,000 (1,1)-swaps from S35 (fast! using incremental tight updates)
    std::mt19937_64 rng(55555ULL);
    std::vector<int> cur = S35;
    std::vector<int> tight(N5, 0);
    for (int u : cur)
        for (int w = 0; w < W5; ++w) {
            uint64_t b = close5[u].w[w];
            while (b) { int bit = __builtin_ctzll(b); b &= b - 1; ++tight[(w << 6) + bit]; }
        }

    int min_forb = 99999;
    std::vector<int> best_I_smallF;
    PrivPair best_pp{0,0,0,99999};

    // Also track best multi-port (b=2..8) code with smallest |F| / b
    struct PortCand {
        int b, forb_sz;
        std::vector<int> I, P0, P1;
    };
    std::vector<PortCand> port_cands;

    for (int step = 0; step < 3000; ++step) {
        if (step % 5 == 0) {
            auto pps = find_private_pairs(cur);
            if (!pps.empty()) {
                if (pps[0].forb_sz < min_forb) {
                    min_forb = pps[0].forb_sz;
                    best_I_smallF = cur;
                    best_pp = pps[0];
                    std::cout << "[walk step=" << step << "] NEW min_forb=" << min_forb
                              << " (num_priv=" << pps.size() << ")" << std::endl;
                }
                if (step % 100 == 0 || pps[0].forb_sz <= 600) {
                    // Build greedy compatible multi-port P0, P1 up to b=8
                    std::vector<int> P0, P1;
                    std::vector<bool> used_s(35, false);
                    for (const auto& pp : pps) {
                        if (used_s[pp.s_idx]) continue;
                        bool ok0 = true;
                        for (size_t i = 0; i < P0.size(); ++i)
                            if (close5[pp.s].test(P0[i]) || close5[pp.q].test(P1[i])) { ok0 = false; break; }
                        if (ok0) { used_s[pp.s_idx] = true; P0.push_back(pp.s); P1.push_back(pp.q); continue; }
                        bool ok1 = true;
                        for (size_t i = 0; i < P0.size(); ++i)
                            if (close5[pp.q].test(P0[i]) || close5[pp.s].test(P1[i])) { ok1 = false; break; }
                        if (ok1) { used_s[pp.s_idx] = true; P0.push_back(pp.q); P1.push_back(pp.s); }
                    }
                    if ((int)P0.size() >= 1) {
                        Bitset5 n0{}, n1{};
                        for (int p : P0) for (int w = 0; w < W5; ++w) n0.w[w] |= close5[p].w[w];
                        for (int p : P1) for (int w = 0; w < W5; ++w) n1.w[w] |= close5[p].w[w];
                        int fsz = 0;
                        for (int w = 0; w < W5; ++w) fsz += __builtin_popcountll(n0.w[w] & n1.w[w]);
                        if ((int)P0.size() == 1 || (int)P0.size() >= 3) {
                            port_cands.push_back({(int)P0.size(), fsz, cur, P0, P1});
                        }
                    }
                }
            }
        }
        std::vector<int> c1;
        for (int v = 0; v < N5; ++v) if (tight[v] == 1) c1.push_back(v);
        if (c1.empty()) break;
        int v = c1[rng() % c1.size()];
        int bi = -1;
        for (int i = 0; i < (int)cur.size(); ++i) if (close5[cur[i]].test(v)) { bi = i; break; }
        int rem = cur[bi];
        cur[bi] = v;
        for (int w = 0; w < W5; ++w) {
            uint64_t diff = close5[rem].w[w] ^ close5[v].w[w];
            while (diff) {
                int bit = __builtin_ctzll(diff); diff &= diff - 1;
                tight[(w << 6) + bit] += ((close5[v].w[w] >> bit) & 1ULL) ? 1 : -1;
            }
        }
    }
    std::cout << "[walk done] min_forb=" << min_forb << " cands=" << port_cands.size()
              << " elapsed=" << std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count() << "s\n";

    // Phase 2: Test ILS on V5 \ F for top candidates!
    // Always test best_I_smallF (b=1, smallest |F|) first, plus top multi-port candidates!
    std::vector<PortCand> to_test;
    if (!best_I_smallF.empty()) {
        to_test.push_back({1, best_pp.forb_sz, best_I_smallF, {best_pp.s}, {best_pp.q}});
    }
    // Also add S35 b=1
    auto pps0 = find_private_pairs(S35);
    to_test.push_back({1, pps0[0].forb_sz, S35, {pps0[0].s}, {pps0[0].q}});

    // Sort port_cands by smallest forb_sz for each b >= 2, pick top 5
    std::sort(port_cands.begin(), port_cands.end(), [](const PortCand& a, const PortCand& b) {
        return (double)a.forb_sz / a.b < (double)b.forb_sz / b.b;
    });
    for (size_t i = 0; i < std::min<size_t>(6, port_cands.size()); ++i) to_test.push_back(port_cands[i]);

    double best_score2 = 35.0 * 35.0;
    PortCand winner;
    std::vector<int> winner_X;
    int win_d = 0, win_h = 0, win_v = 0;

    for (const auto& pc : to_test) {
        Bitset5 n0{}, n1{}, forb{};
        for (int p : pc.P0) for (int w = 0; w < W5; ++w) n0.w[w] |= close5[p].w[w];
        for (int p : pc.P1) for (int w = 0; w < W5; ++w) n1.w[w] |= close5[p].w[w];
        for (int w = 0; w < W5; ++w) forb.w[w] = n0.w[w] & n1.w[w];

        int target_c = 35; // aim for 35 first!
        auto X = search_indep_avoiding_F(forb, S35, target_c, 3500);
        int c = (int)X.size();
        double sc = (double)(35 - pc.b) * (35 - pc.b) + 2.0 * pc.b * c;
        int d = 0, h = 0, v = 0;
        for (int x : X) {
            bool in0 = n0.test(x), in1 = n1.test(x);
            if (!in0 && !in1) ++d;
            else if (in0 && !in1) ++h;
            else if (in1 && !in0) ++v;
        }
        std::cout << "[test b=" << pc.b << " |F|=" << pc.forb_sz << "] got c=" << c
                  << " (d=" << d << ", h=" << h << ", v=" << v << ") a2=" << (long long)sc << std::endl;
        if (sc > best_score2 + 1e-9) {
            best_score2 = sc;
            winner = pc;
            winner_X = X;
            win_d = d; win_h = h; win_v = v;
        }
    }

    if (!winner_X.empty()) {
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
        out << "  \"a\": 35, \"b\": " << winner.b << ", \"c\": " << winner_X.size()
            << ", \"d\": " << win_d << ", \"h\": " << win_h << ", \"v\": " << win_v << ",\n";
        write_list("I", winner.I); out << ",\n";
        write_list("P0", winner.P0); out << ",\n";
        write_list("P1", winner.P1); out << ",\n";
        write_list("X", winner_X); out << "\n}\n";
        std::cout << "[WINNER] Saved d5_gadget_best.json! a2=" << (long long)best_score2
                  << " (" << std::pow(best_score2, 0.1) << ")\n";
    }
    return 0;
}
