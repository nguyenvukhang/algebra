from os import listdir

tbl = []

for filename in listdir("."):
    if not filename.endswith(".lean"):
        continue
    with open(filename, "r") as f:
        text = f.read()
        line = text.splitlines()[0]
    assert line.startswith("-- Dummit & Foote, ")
    line = line.removeprefix("-- Dummit & Foote, ").strip()
    tbl.append((filename, line))

tbl.sort(key=lambda v: v[1])

with open("README", "w") as f:
    for filename, line in tbl:
        print(filename, "::", line, file=f)
