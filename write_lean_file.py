import json
import sys

# 从命令行获取第一个参数，如果没有提供则默认为 0
idx = int(sys.argv[1]) if len(sys.argv) > 1 else 0

with open("/data1/zzh/verina/verina_lemmas_quickchecked.json", "r") as f:
    data = json.load(f)




text = data[idx]["header"].replace("import Mathlib", "import Codetic") + "\n" + \
       data[idx]["lemma_formal_statements"].replace("sorry", "\n  codetic?\n  codetic?(config := { useDefaultSimpSet := false })")

with open(f"/data1/zzh/codetic/lemmas_quickchecked_{idx}.lean", "w") as f:
    f.write(text)

print(f"Successfully generated file at index {idx}")