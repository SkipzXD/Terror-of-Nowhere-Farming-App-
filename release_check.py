"""
Release check for the PUBLIC build of ToN Toolkit.

Run by build_release.bat after the build, before anything is zipped.
Exits non-zero (so nothing is packaged) if something is missing, private,
or cluttering the folder users open.

  * Beside the exe users should only see the exe, _internal and the three
    documents. Everything else lives inside _internal.
  * The terror picker's data must be packed in _internal: terror_names.json
    with its round lists, icon positions and 8 Pages table, and both sheets.
  * Nothing personal may ship: personal.txt (turns on the AFK Helper) and
    ton_toolkit.json (your own settings) must not exist anywhere.
"""
import json
import os
import sys

TOP_LEVEL = {"ToNToolkit.exe", "_internal", "LICENSE", "README.md",
             "DISCLAIMER.md"}
DATA = "terror_names.json"
PRIVATE = {"personal.txt", "ton_toolkit.json"}


def main(dist):
    problems = []

    # 1. private files, anywhere in the build
    for root, _dirs, files in os.walk(dist):
        for name in files:
            if name.lower() in PRIVATE:
                problems.append(f"{os.path.join(root, name)}: private, "
                                f"must not be published")

    # 2. a tidy top level
    for name in sorted(os.listdir(dist)):
        if name not in TOP_LEVEL:
            problems.append(f"{os.path.join(dist, name)}: should not sit "
                            f"beside the exe (it belongs in _internal)")

    # 3. the picker's data, packed inside _internal
    internal = os.path.join(dist, "_internal")
    path = os.path.join(internal, DATA)
    if not os.path.isfile(path):
        problems.append(f"{path}: missing - the terror picker needs it")
    else:
        try:
            with open(path, encoding="utf-8") as f:
                d = json.load(f)
            for key in ("names", "rounds", "sprites", "eight_pages"):
                if not d.get(key):
                    problems.append(f"{path}: has no '{key}' - use the "
                                    f"complete terror_names.json")
            for sheet in d.get("sprite_sheets") or []:
                if not os.path.isfile(os.path.join(internal, sheet)):
                    problems.append(f"{os.path.join(internal, sheet)}: "
                                    f"missing (named in {DATA})")
        except (OSError, ValueError) as e:
            problems.append(f"{path}: unreadable ({e})")

    if problems:
        print()
        print("  RELEASE CHECK FAILED - nothing will be zipped:")
        for p in problems:
            print(f"    - {p}")
        return 1
    print("  release check passed")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1] if len(sys.argv) > 1 else
                  os.path.join("dist", "ToNToolkit")))
