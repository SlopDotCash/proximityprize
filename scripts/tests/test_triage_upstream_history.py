"""The squash-merge bot must leave upstream synchronizations to a maintainer."""
from pathlib import Path
import re
import unittest


ROOT = Path(__file__).resolve().parents[2]
WORKFLOW = ROOT / ".github/workflows/claude-pr-triage.yml"


class TriageUpstreamHistory(unittest.TestCase):
    def test_both_verdict_paths_protect_the_upstream_inventory(self):
        text = WORKFLOW.read_text()
        patterns = re.findall(r"if grep -Eq '([^']+)'", text)
        self.assertEqual(len(patterns), 2)
        for pattern in patterns:
            for path in (
                ".github/workflows/ci.yml", "DISPROOF_LOG.md", "CLAUDE.md", "AGENTS.md",
                "lean-toolchain", "lakefile.toml", ".gitmodules", "scripts/arklib-upstream.json",
            ):
                with self.subTest(pattern=pattern, path=path):
                    self.assertIsNotNone(re.search(pattern, path))
            self.assertIsNone(re.search(pattern, "scripts/arklib-upstream.json.example"))

    def test_draft_pull_requests_are_not_automatically_triaged(self):
        self.assertIn(
            "if: github.event_name == 'workflow_dispatch' || !github.event.pull_request.draft",
            WORKFLOW.read_text(),
        )


if __name__ == "__main__":
    unittest.main()
