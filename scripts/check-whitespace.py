#!/usr/bin/env python3
"""Check repository text hygiene without external formatting dependencies.

This is not a Lean source formatter: alignment and syntax layout are not checked.
Pass file paths to check only those files; otherwise check repository-owned text
files known to Git, including untracked files that are not ignored.
"""

from pathlib import Path
import subprocess
import sys


ROOT = Path(__file__).resolve().parent.parent
TEXT_SUFFIXES = {".json", ".lean", ".md", ".py", ".sh", ".yaml", ".yml"}
TEXT_NAMES = {".editorconfig", ".gitignore", "LICENSE", "lean-toolchain"}
UPSTREAM_FILES = {"spec/LICENSE", "spec/bip-0093.mediawiki"}


def repository_files():
  output = subprocess.check_output(
    ["git", "ls-files", "-z", "--cached", "--others", "--exclude-standard"],
    cwd=ROOT,
  )
  for name in sorted(set(output.decode("utf-8").split("\0")) - {""}):
    path = ROOT / name
    if name not in UPSTREAM_FILES and path.is_file():
      if path.suffix in TEXT_SUFFIXES or path.name in TEXT_NAMES:
        yield path


def check(path):
  errors = []
  try:
    contents = path.read_bytes().decode("utf-8")
  except (OSError, UnicodeDecodeError) as error:
    return [f"{path}: {error}"]
  if contents.startswith("\ufeff"):
    errors.append(f"{path}: UTF-8 byte order mark is not allowed")
  if contents and not contents.endswith("\n"):
    errors.append(f"{path}: missing final newline")
  for number, line in enumerate(contents.split("\n"), start=1):
    for invalid, message in (("\r", "use LF line endings"), ("\t", "use spaces, not tabs")):
      if invalid in line:
        errors.append(f"{path}:{number}: {message}")
    if line.rstrip(" \t\r") != line:
      errors.append(f"{path}:{number}: trailing whitespace")
  return errors


def main():
  paths = list(map(Path, sys.argv[1:])) if len(sys.argv) > 1 else repository_files()
  errors = [error for path in paths for error in check(path)]
  if errors:
    print("\n".join(errors), file=sys.stderr)
    return 1
  print("Whitespace check passed.")
  return 0


if __name__ == "__main__":
  sys.exit(main())
