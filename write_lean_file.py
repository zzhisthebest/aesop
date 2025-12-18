import json

with open("/data1/zzh/verina/verina_lemmas_quickchecked.json", "r") as f:
    data = json.load(f)

paixu=2260
idx=paixu-1
text=data[idx]["header"].replace("import Mathlib", "import Aesop")+"\n"+data[idx]["lemma_formal_statements"].replace("sorry","\n  aesop?\n  aesop?(config := { useDefaultSimpSet := false })")
with open(f"/data1/zzh/aesop/lemmas_quickchecked_{idx}.lean", "w") as f:
    f.write(text)