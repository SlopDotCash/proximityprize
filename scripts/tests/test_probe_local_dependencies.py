"""Catch deletion of statically imported local probe helpers without running probes."""
import ast
from pathlib import Path
import unittest
import warnings


class ProbeLocalDependencies(unittest.TestCase):
    def test_named_probe_imports_resolve(self):
        root = Path(__file__).resolve().parents[1] / 'probes'
        missing = []
        with warnings.catch_warnings():
            warnings.simplefilter('ignore', SyntaxWarning)
            for source in sorted(root.glob('*.py')):
                tree = ast.parse(source.read_text(), filename=str(source))
                for node in ast.walk(tree):
                    if isinstance(node, ast.ImportFrom) and node.module:
                        modules = [node.module]
                    elif isinstance(node, ast.Import):
                        modules = [alias.name for alias in node.names]
                    else:
                        continue
                    for module in modules:
                        name = module.split('.')[0]
                        if not name.startswith(('probe_', '_skeptic_')):
                            continue
                        if not (root / (name + '.py')).is_file() and not (root / name / '__init__.py').is_file():
                            missing.append(f'{source.name}:{node.lineno}: {module}')
        self.assertEqual(missing, [], '\n'.join(missing))


if __name__ == '__main__':
    unittest.main()
