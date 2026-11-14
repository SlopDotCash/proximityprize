// Exhaustive assignment oracle for the finite-state optimizer.
#define main exact_jump_probe_main
#include "../probes/probe_rate_quarter_exact_jump_multiline.cpp"
#undef main
#include <functional>

int main() {
  {
    const Context ctx{65537};
    const int generator = ctx.primitive_root();
    std::array<int, 16> mu{};
    for (int i = 0; i < 16; ++i) mu[i] = ctx.power(generator, (65536 / 16) * i);
    const Poly split = ctx.scale(65536, ctx.locator({0, 1, 2}, mu));
    // Reconstruct the different polynomial with the old overflowing key.
    std::uint64_t packed = 0;
    for (int i = 3; i >= 0; --i) packed = packed * 65537 + split[i];
    Poly nonsplit{};
    for (int i = 0; i < 4; ++i) {
      nonsplit[i] = packed % 65537;
      packed /= 65537;
    }
    if (split == nonsplit) throw std::runtime_error("collision fixture is not distinct");
    int split_count = 0, other_count = 0;
    for (int x : mu) {
      split_count += ctx.eval(split, x) == 0;
      other_count += ctx.eval(nonsplit, x) == 0;
    }
    if (split_count != 3 || other_count != 0)
      throw std::runtime_error("independent root census mismatch");
    SplitRoots index{{split, {0, 1, 2}}};
    if (!index.count(split) || index.count(nonsplit))
      throw std::runtime_error("polynomial lookup confuses distinct root sets");
    // The new ordering retains the old high-coefficient-first order without
    // relying on an integer encoding that may overflow.
    if (!polynomial_less(nonsplit, split))
      throw std::runtime_error("coefficient ordering mismatch");
  }
  {
    const Context ctx{2147483647};
    const Poly a{2147483646, 0, 1, 2147483646};
    if (ctx.add(a, a) != Poly{2147483645, 0, 2, 2147483645})
      throw std::runtime_error("coefficient addition overflow");
  }
  const std::vector<Pattern> patterns = {
      {{15}}, {{1, 14}}, {{3, 12}}, {{1, 2, 12}}, {{1, 2, 4, 8}}};
  int checked = 0;
  for (const auto& a : patterns) for (const auto& b : patterns)
    for (const auto& c : patterns) {
      const std::vector<Pattern> coordinates{a, b, c};
      for (int target = 0; target <= 4; ++target)
        for (int budget = 0; budget <= 2; ++budget) {
          int best = -1;
          std::function<void(int, std::array<int, 4>, int, int)> visit;
          visit = [&](int step, std::array<int, 4> cores, int roots, int labels) {
            if (roots > budget) return;
            if (step == 3) {
              if (*std::min_element(cores.begin(), cores.end()) >= target)
                best = std::max(best, labels);
              return;
            }
            // Build choices directly from their mathematical interpretation,
            // without invoking the optimizer's choices_for helper.
            auto choose = [&](int mask, int value, int root) {
              auto next = cores;
              for (int line = 0; line < 4; ++line) next[line] += (mask >> line) & 1;
              visit(step + 1, next, roots + root, labels + value);
            };
            for (int mask : coordinates[step].components)
              choose(mask, mask == 15 ? 0 : 1, 0);
            choose(0, coordinates[step].components.size(), 0);
            choose(15, 0, 1);
            choose(0, 1, 1);
          };
          visit(0, {0, 0, 0, 0}, 0, 0);
          std::vector<Choice> assignment;
          auto actual = solve_exact(coordinates, target, budget, &assignment);
          if (actual.labels != best) throw std::runtime_error("exhaustive optimum mismatch");
          if (best >= 0) {
            std::array<int, 4> cores{};
            int labels = 0, roots = 0;
            for (const auto& choice : assignment) {
              labels += choice.labels; roots += choice.root_cost;
              for (int line = 0; line < 4; ++line) cores[line] += (choice.mask >> line) & 1;
            }
            if (assignment.size() != 3 || labels != best || roots > budget ||
                *std::min_element(cores.begin(), cores.end()) < target)
              throw std::runtime_error("assignment witness mismatch");
          }
          ++checked;
        }
    }
  std::cout << "PASS " << checked << " exhaustive DP comparisons\n";
}
