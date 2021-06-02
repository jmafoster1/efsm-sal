lines = []
with open("output.txt") as f:
    for line in f:
        line = line.strip()
        if (line.endswith("\"") or line.endswith("oops")) and line.count("lemma") == 1:
            lines.append(line)
with open("output.txt", 'w') as f:
    for line in lines:
        print(line, file=f)
