"""Tests for knowledge-base review context resolution."""
import sys
import unittest
from pathlib import Path

SCRIPTS_DIR = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPTS_DIR / "kb"))
import review_context


class ReviewContextTests(unittest.TestCase):
    def test_normalize_repo_path_posix_slashes(self):
        # Relative with forward slashes
        self.assertEqual(
            review_context.normalize_repo_path("ArkLib/Data/Basic.lean"),
            "ArkLib/Data/Basic.lean",
        )
        # Relative with backslashes
        self.assertEqual(
            review_context.normalize_repo_path(r"ArkLib\Data\Basic.lean"),
            "ArkLib/Data/Basic.lean",
        )
        # Absolute path within REPO_ROOT
        abs_path = review_context.REPO_ROOT / "ArkLib" / "Data" / "Basic.lean"
        self.assertEqual(
            review_context.normalize_repo_path(str(abs_path)),
            "ArkLib/Data/Basic.lean",
        )

    def test_infer_keys_from_files_with_platform_paths(self):
        citations_payload = {
            "files": {
                "ArkLib/Data/Basic.lean": ["PaperA"],
                "Research/ProximityPrize/Core.lean": ["PaperB", "PaperC"],
            }
        }
        # Slashes and backslashes should both resolve to the correct keys
        keys = review_context.infer_keys_from_files(
            [r"ArkLib\Data\Basic.lean", "Research/ProximityPrize/Core.lean"],
            citations_payload,
        )
        self.assertEqual(keys, {"PaperA", "PaperB", "PaperC"})

    def test_parse_csv_items(self):
        self.assertEqual(
            review_context.parse_csv_items(["key1, key2", "key3"]),
            ["key1", "key2", "key3"],
        )

    def test_unique_in_order(self):
        self.assertEqual(
            review_context.unique_in_order(["b", "a", "b", "c", "a"]),
            ["b", "a", "c"],
        )


if __name__ == "__main__":
    unittest.main()
