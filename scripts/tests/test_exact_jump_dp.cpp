// Exhaustive assignment oracle for the finite-state optimizer.
#define main exact_jump_probe_main
#include "../probes/probe_rate_quarter_exact_jump_multiline.cpp"
#undef main
#include <functional>

int main() {
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
