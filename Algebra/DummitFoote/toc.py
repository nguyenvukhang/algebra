from os import listdir, path

__cwd__ = path.dirname(__file__)

tbl = []

for filename in listdir(__cwd__):
    if not filename.endswith(".lean"):
        continue
    with open(path.join(__cwd__, filename), "r") as f:
        text = f.read()
        line = text.splitlines()[0]
    assert line.startswith("-- Dummit & Foote, ")
    line = line.removeprefix("-- Dummit & Foote, ").strip()
    tbl.append((filename, line))

tbl.sort(key=lambda v: v[1])

with open(path.join(__cwd__, "README"), "w") as f:
    for filename, line in tbl:
        print(filename, "::", line, file=f)
