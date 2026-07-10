/*
 * Exact red-team search for the first agreement lattice point beyond the
 * saturated rate-quarter construction.
 *
 * Compile:
 *   c++ -O3 -std=c++20 -o /tmp/exact_jump_multiline \
 *     scripts/probes/probe_rate_quarter_exact_jump_multiline.cpp
 *
 * Run:
 *   /tmp/exact_jump_multiline 97 32 18 fixed
 *   /tmp/exact_jump_multiline 97 32 18 all
 *   /tmp/exact_jump_multiline 193 64 36 all
 *
 * The source lines have the determinant-collapsed form
 *
 *   (X h_i, h_i),   h_i = G(X) f_i(X^m),   m=n/16,
 *
 * where 0,f_1,f_2,f_3 are a four-clique of cubic polynomials whose six
 * differences split on mu_16.  The fixed universal triangle is extended by
 * every fourth line over the requested field.  The common locator G may use
 * at most m-2 domain roots, exactly the degree left by X*h_i < n/4.
 *
 * For every clique, a dense finite-state dynamic program makes an exact
 * integral choice at every domain coordinate: own one polynomial-value
 * component, make a hole, or spend one common-locator root.  It maximizes the
 * number of abstract one-fresh labels subject to every source core having
 * size at least agreement-1.  A hole is worth the number of distinct values,
 * not blindly four labels.  Thus this is an exact architecture census, not a
 * fractional LP and not a claim about arbitrary received stacks.
 */

#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <map>
#include <numeric>
#include <set>
#include <stdexcept>
#include <string>
#include <tuple>
#include <unordered_map>
#include <utility>
#include <vector>

using Poly = std::array<int, 4>;

struct Context {
  int p;

  int mod(long long x) const {
    x %= p;
    if (x < 0) x += p;
    return static_cast<int>(x);
  }

  int power(int a, long long e) const {
    long long out = 1;
    long long b = mod(a);
    while (e) {
      if (e & 1) out = out * b % p;
      b = b * b % p;
      e >>= 1;
    }
    return static_cast<int>(out);
  }

  int inverse(int a) const {
    if (mod(a) == 0) throw std::runtime_error("division by zero");
    return power(a, p - 2);
  }

  int primitive_root() const {
    int n = p - 1;
    std::vector<int> factors;
    for (int q = 2; q * q <= n; ++q) {
      if (n % q != 0) continue;
      factors.push_back(q);
      while (n % q == 0) n /= q;
    }
    if (n > 1) factors.push_back(n);
    for (int g = 2; g < p; ++g) {
      bool ok = true;
      for (int q : factors) {
        if (power(g, (p - 1) / q) == 1) {
          ok = false;
          break;
        }
      }
      if (ok) return g;
    }
    throw std::runtime_error("no primitive root");
  }

  Poly add(const Poly& a, const Poly& b) const {
    Poly out{};
    for (int i = 0; i < 4; ++i) out[i] = mod(a[i] + b[i]);
    return out;
  }

  Poly sub(const Poly& a, const Poly& b) const {
    Poly out{};
    for (int i = 0; i < 4; ++i) out[i] = mod(a[i] - b[i]);
    return out;
  }

  Poly scale(int s, const Poly& a) const {
    Poly out{};
    for (int i = 0; i < 4; ++i) out[i] = mod(static_cast<long long>(s) * a[i]);
    return out;
  }

  int eval(const Poly& a, int x) const {
    int out = 0;
    for (int i = 3; i >= 0; --i) out = mod(static_cast<long long>(out) * x + a[i]);
    return out;
  }

  std::uint64_t key(const Poly& a) const {
    std::uint64_t out = 0;
    for (int i = 3; i >= 0; --i) out = out * p + a[i];
    return out;
  }

  Poly locator(const std::array<int, 3>& roots,
               const std::array<int, 16>& mu) const {
    std::vector<int> out{1};
    for (int e : roots) {
      std::vector<int> next(out.size() + 1, 0);
      for (std::size_t i = 0; i < out.size(); ++i) {
        next[i] = mod(next[i] - static_cast<long long>(mu[e]) * out[i]);
        next[i + 1] = mod(next[i + 1] + out[i]);
      }
      out.swap(next);
    }
    if (out.size() != 4 || out[3] != 1) throw std::runtime_error("bad locator");
    return Poly{out[0], out[1], out[2], out[3]};
  }
};

struct Pattern {
  std::vector<int> components;  // four-bit line masks

  int code() const {
    int out = static_cast<int>(components.size());
    int shift = 4;
    for (int mask : components) {
      out |= mask << shift;
      shift += 4;
    }
    return out;
  }
};

struct Choice {
  int mask;       // lines whose cores acquire this coordinate
  int labels;     // new abstract labels charged at this coordinate
  int root_cost;  // whether this coordinate is made a root of G

  auto tie() const { return std::tuple(mask, labels, root_cost); }
};

struct SolveResult {
  int labels = -1;
  int used_roots = -1;
  std::size_t reachable_states = 0;
};

static std::vector<Choice> choices_for(const Pattern& pattern, int root_budget) {
  std::vector<Choice> out;
  for (int component : pattern.components) {
    out.push_back({component, component == 15 ? 0 : 1, 0});
  }
  out.push_back({0, static_cast<int>(pattern.components.size()), 0});
  if (root_budget > 0) {
    out.push_back({15, 0, 1});
    out.push_back({0, 1, 1});
  }
  std::sort(out.begin(), out.end(), [](const Choice& a, const Choice& b) {
    return a.tie() < b.tie();
  });
  out.erase(std::unique(out.begin(), out.end(), [](const Choice& a, const Choice& b) {
    return a.tie() == b.tie();
  }), out.end());
  return out;
}

static SolveResult solve_exact(const std::vector<Pattern>& coordinates,
                               int core_target, int root_budget,
                               std::vector<Choice>* assignment = nullptr) {
  const int b = core_target + 1;
  const int gb = root_budget + 1;
  const std::size_t state_count =
      static_cast<std::size_t>(b) * b * b * b * gb;
  std::vector<std::int16_t> current(state_count, -1), next(state_count, -1);
  std::vector<std::uint32_t> active{0}, next_active;
  std::vector<std::vector<std::uint32_t>> parents;
  std::vector<std::vector<std::uint8_t>> parent_choices;
  if (assignment != nullptr) {
    parents.assign(coordinates.size(),
                   std::vector<std::uint32_t>(state_count, UINT32_MAX));
    parent_choices.assign(coordinates.size(),
                          std::vector<std::uint8_t>(state_count, UINT8_MAX));
  }
  current[0] = 0;

  auto encode = [b, gb](int c0, int c1, int c2, int c3, int g) {
    std::size_t q = c0;
    q = q * b + c1;
    q = q * b + c2;
    q = q * b + c3;
    return q * gb + g;
  };

  for (std::size_t step = 0; step < coordinates.size(); ++step) {
    const Pattern& pattern = coordinates[step];
    const std::vector<Choice> choices = choices_for(pattern, root_budget);
    next_active.clear();
    next_active.reserve(std::min(state_count, active.size() * choices.size()));
    for (std::uint32_t packed : active) {
      std::size_t q = packed;
      const int g = static_cast<int>(q % gb);
      q /= gb;
      const int c3 = static_cast<int>(q % b); q /= b;
      const int c2 = static_cast<int>(q % b); q /= b;
      const int c1 = static_cast<int>(q % b); q /= b;
      const int c0 = static_cast<int>(q);
      const int old_value = current[packed];
      for (std::size_t choice_index = 0; choice_index < choices.size(); ++choice_index) {
        const Choice& choice = choices[choice_index];
        if (g + choice.root_cost > root_budget) continue;
        const int d0 = std::min(core_target, c0 + ((choice.mask >> 0) & 1));
        const int d1 = std::min(core_target, c1 + ((choice.mask >> 1) & 1));
        const int d2 = std::min(core_target, c2 + ((choice.mask >> 2) & 1));
        const int d3 = std::min(core_target, c3 + ((choice.mask >> 3) & 1));
        const std::size_t target = encode(d0, d1, d2, d3, g + choice.root_cost);
        const int value = old_value + choice.labels;
        if (value <= next[target]) continue;
        if (next[target] < 0) next_active.push_back(static_cast<std::uint32_t>(target));
        next[target] = static_cast<std::int16_t>(value);
        if (assignment != nullptr) {
          parents[step][target] = packed;
          parent_choices[step][target] = static_cast<std::uint8_t>(choice_index);
        }
      }
    }
    for (std::uint32_t packed : active) current[packed] = -1;
    current.swap(next);
    active.swap(next_active);
  }

  SolveResult result;
  result.reachable_states = active.size();
  for (int g = 0; g <= root_budget; ++g) {
    const std::size_t target = encode(core_target, core_target,
                                      core_target, core_target, g);
    if (current[target] > result.labels) {
      result.labels = current[target];
      result.used_roots = g;
    }
  }
  if (assignment != nullptr && result.labels >= 0) {
    assignment->assign(coordinates.size(), Choice{-1, -1, -1});
    std::uint32_t state = static_cast<std::uint32_t>(
        encode(core_target, core_target, core_target, core_target,
               result.used_roots));
    for (std::size_t reverse = coordinates.size(); reverse > 0; --reverse) {
      const std::size_t step = reverse - 1;
      const std::uint8_t choice_index = parent_choices[step][state];
      if (choice_index == UINT8_MAX) throw std::runtime_error("missing DP parent");
      const std::vector<Choice> choices = choices_for(coordinates[step], root_budget);
      (*assignment)[step] = choices.at(choice_index);
      state = parents[step][state];
    }
    if (state != 0) throw std::runtime_error("DP path did not return to origin");
  }
  return result;
}

static Pattern collision_pattern(const Context& ctx,
                                 const std::array<Poly, 4>& fs, int x) {
  std::map<int, int> buckets;
  for (int i = 0; i < 4; ++i) buckets[ctx.eval(fs[i], x)] |= 1 << i;
  Pattern out;
  for (const auto& [_, mask] : buckets) out.components.push_back(mask);
  std::sort(out.components.begin(), out.components.end());
  return out;
}

static std::string signature_of(const std::vector<Pattern>& quotient_patterns) {
  std::map<int, int> counts;
  for (const Pattern& pattern : quotient_patterns) ++counts[pattern.code()];
  std::string out;
  for (const auto& [code, count] : counts) {
    out += std::to_string(code) + ":" + std::to_string(count) + ";";
  }
  return out;
}

static std::string canonical_signature(
    const std::vector<Pattern>& quotient_patterns) {
  std::array<int, 4> permutation{0, 1, 2, 3};
  std::string best;
  bool first = true;
  do {
    std::vector<Pattern> renamed;
    renamed.reserve(quotient_patterns.size());
    for (const Pattern& pattern : quotient_patterns) {
      Pattern next;
      for (int mask : pattern.components) {
        int renamed_mask = 0;
        for (int i = 0; i < 4; ++i) {
          if ((mask >> i) & 1) renamed_mask |= 1 << permutation[i];
        }
        next.components.push_back(renamed_mask);
      }
      std::sort(next.components.begin(), next.components.end());
      renamed.push_back(next);
    }
    const std::string candidate = signature_of(renamed);
    if (first || candidate < best) {
      first = false;
      best = candidate;
    }
  } while (std::next_permutation(permutation.begin(), permutation.end()));
  return best;
}

int main(int argc, char** argv) {
  if (argc != 4 && argc != 5) {
    std::cerr << "usage: " << argv[0]
              << " <prime> <n> <agreement> [fixed|all]\n";
    return 2;
  }
  const int p = std::atoi(argv[1]);
  const int n = std::atoi(argv[2]);
  const int agreement = std::atoi(argv[3]);
  const std::string mode = argc == 5 ? argv[4] : "fixed";
  if (mode != "fixed" && mode != "all") {
    throw std::runtime_error("mode must be fixed or all");
  }
  if ((p - 1) % 16 != 0 || n % 16 != 0 || (p - 1) % n != 0) {
    throw std::runtime_error("need n | p-1 and 16 | n");
  }
  const int m = n / 16;
  const int k = n / 4;
  const int core_target = agreement - 1;
  const int root_budget = std::max(0, m - 2);
  const Context ctx{p};
  const int generator = ctx.primitive_root();
  const int zeta = ctx.power(generator, (p - 1) / 16);
  std::array<int, 16> mu{};
  for (int e = 0; e < 16; ++e) mu[e] = ctx.power(zeta, e);

  std::vector<std::array<int, 3>> triples;
  std::vector<Poly> monic;
  std::unordered_map<std::uint64_t, std::array<int, 3>> split_roots;
  std::vector<Poly> split_polynomials;
  for (int a = 0; a < 16; ++a) {
    for (int b = a + 1; b < 16; ++b) {
      for (int c = b + 1; c < 16; ++c) {
        const std::array<int, 3> roots{a, b, c};
        const Poly locator = ctx.locator(roots, mu);
        triples.push_back(roots);
        monic.push_back(locator);
        for (int scalar = 1; scalar < p; ++scalar) {
          const Poly polynomial = ctx.scale(scalar, locator);
          split_roots[ctx.key(polynomial)] = roots;
          split_polynomials.push_back(polynomial);
        }
      }
    }
  }

  auto canonical_dihedral_roots = [](const std::array<int, 3>& roots) {
    std::array<int, 3> best{16, 16, 16};
    for (int sign : {-1, 1}) {
      for (int shift = 0; shift < 16; ++shift) {
        std::array<int, 3> image{};
        for (int i = 0; i < 3; ++i) {
          int value = (sign * roots[i] + shift) % 16;
          if (value < 0) value += 16;
          image[i] = value;
        }
        std::sort(image.begin(), image.end());
        best = std::min(best, image);
      }
    }
    return best;
  };
  std::vector<Poly> monic_orbit_representatives;
  for (std::size_t i = 0; i < triples.size(); ++i) {
    if (triples[i] == canonical_dihedral_roots(triples[i])) {
      monic_orbit_representatives.push_back(monic[i]);
    }
  }

  const Poly zero{0, 0, 0, 0};
  const Poly pa = ctx.locator({0, 1, 8}, mu);
  const Poly pb = ctx.locator({2, 9, 10}, mu);
  const Poly pc = ctx.locator({3, 5, 7}, mu);
  int pivot = -1;
  for (int j = 0; j < 3; ++j) {
    if (pa[j] != pb[j]) {
      pivot = j;
      break;
    }
  }
  if (pivot < 0) throw std::runtime_error("locator pivot missing");
  const int lambda = ctx.mod(static_cast<long long>(pc[pivot] - pa[pivot]) *
                             ctx.inverse(ctx.mod(pb[pivot] - pa[pivot])));
  const Poly line_a = ctx.scale(ctx.mod(1 - lambda), pa);
  const Poly line_b = pc;
  if (ctx.add(line_a, ctx.scale(lambda, pb)) != pc) {
    throw std::runtime_error("fixed triangle identity failed");
  }

  std::vector<Poly> extensions;
  for (const Poly& candidate : split_polynomials) {
    if (candidate == line_a || candidate == line_b) continue;
    if (!split_roots.count(ctx.key(ctx.sub(candidate, line_a)))) continue;
    if (!split_roots.count(ctx.key(ctx.sub(candidate, line_b)))) continue;
    extensions.push_back(candidate);
  }
  std::sort(extensions.begin(), extensions.end(), [&ctx](const Poly& a, const Poly& b) {
    return ctx.key(a) < ctx.key(b);
  });
  extensions.erase(std::unique(extensions.begin(), extensions.end()), extensions.end());

  struct Candidate {
    std::array<Poly, 4> fs;
    std::vector<Pattern> quotient_patterns;
  };
  std::map<std::string, Candidate> candidates;
  std::uint64_t raw_cliques = 0;
  auto record_candidate = [&](const std::array<Poly, 4>& fs) {
    std::vector<Pattern> quotient_patterns;
    for (int e = 0; e < 16; ++e) {
      quotient_patterns.push_back(collision_pattern(ctx, fs, mu[e]));
    }
    const std::string signature = canonical_signature(quotient_patterns);
    candidates.try_emplace(signature, Candidate{fs, quotient_patterns});
    ++raw_cliques;
  };

  if (mode == "fixed") {
    for (const Poly& extension : extensions) {
      record_candidate({zero, line_a, line_b, extension});
    }
  } else {
    for (const Poly& first_line : monic_orbit_representatives) {
      std::vector<Poly> neighbors;
      for (const Poly& candidate : split_polynomials) {
        if (candidate == first_line) continue;
        if (split_roots.count(ctx.key(ctx.sub(candidate, first_line)))) {
          neighbors.push_back(candidate);
        }
      }
      std::sort(neighbors.begin(), neighbors.end(),
                [&ctx](const Poly& a, const Poly& b) {
                  return ctx.key(a) < ctx.key(b);
                });
      neighbors.erase(std::unique(neighbors.begin(), neighbors.end()),
                      neighbors.end());
      if (first_line == monic_orbit_representatives.front()) {
        std::cerr << "first normalized direction has " << neighbors.size()
                  << " split-cubic neighbors\n";
      }
      for (std::size_t i = 0; i < neighbors.size(); ++i) {
        for (std::size_t j = i + 1; j < neighbors.size(); ++j) {
          if (!split_roots.count(ctx.key(ctx.sub(neighbors[j], neighbors[i])))) {
            continue;
          }
          record_candidate({zero, first_line, neighbors[i], neighbors[j]});
        }
      }
    }
  }

  std::map<std::string, SolveResult> cache;
  int best_labels = -1;
  SolveResult best_result;
  std::array<Poly, 4> best_fs{};
  std::vector<Pattern> best_patterns;
  std::string best_signature;
  for (const auto& [signature, candidate] : candidates) {
    std::vector<Pattern> coordinates;
    coordinates.reserve(n);
    for (const Pattern& pattern : candidate.quotient_patterns) {
      for (int j = 0; j < m; ++j) coordinates.push_back(pattern);
    }
    const SolveResult result = solve_exact(coordinates, core_target, root_budget);
    cache.emplace(signature, result);
    if (result.labels > best_labels) {
      best_labels = result.labels;
      best_result = result;
      best_fs = candidate.fs;
      best_patterns = candidate.quotient_patterns;
      best_signature = signature;
    }
  }

  std::vector<Choice> best_assignment;
  if (best_labels >= 0 && n <= 32) {
    std::vector<Pattern> coordinates;
    coordinates.reserve(n);
    for (const Pattern& pattern : best_patterns) {
      for (int j = 0; j < m; ++j) coordinates.push_back(pattern);
    }
    const SolveResult replay = solve_exact(
        coordinates, core_target, root_budget, &best_assignment);
    if (replay.labels != best_labels) throw std::runtime_error("DP replay mismatch");
  }

  std::cout << "{\n";
  std::cout << "  \"p\": " << p << ", \"n\": " << n
            << ", \"k\": " << k << ", \"m\": " << m << ",\n";
  std::cout << "  \"agreement\": " << agreement
            << ", \"core_target\": " << core_target
            << ", \"common_root_budget\": " << root_budget << ",\n";
  std::cout << "  \"mode\": \"" << mode << "\",\n";
  std::cout << "  \"fixed_triangle_extensions\": " << extensions.size()
            << ", \"normalized_direction_orbits\": "
            << monic_orbit_representatives.size()
            << ", \"raw_normalized_cliques\": " << raw_cliques
            << ", \"partition_signatures\": " << cache.size() << ",\n";
  std::cout << "  \"best_abstract_labels\": " << best_labels
            << ", \"beats_n\": " << (best_labels > n ? "true" : "false")
            << ", \"used_common_roots\": " << best_result.used_roots << ",\n";
  std::cout << "  \"best_polynomial_lines\": [";
  if (best_labels >= 0) {
    for (int i = 0; i < 4; ++i) {
      if (i) std::cout << ", ";
      std::cout << "[";
      for (int j = 0; j < 4; ++j) {
        if (j) std::cout << ", ";
        std::cout << best_fs[i][j];
      }
      std::cout << "]";
    }
  }
  std::cout << "],\n  \"best_partition_signature\": \""
            << best_signature << "\",\n"
            << "  \"best_raw_partition_signature\": \""
            << signature_of(best_patterns) << "\",\n";
  std::cout << "  \"best_assignment\": [";
  for (std::size_t i = 0; i < best_assignment.size(); ++i) {
    if (i) std::cout << ", ";
    const Choice& choice = best_assignment[i];
    std::cout << "[" << choice.mask << ", " << choice.labels
              << ", " << choice.root_cost << "]";
  }
  std::cout << "]\n}\n";
  return 0;
}
