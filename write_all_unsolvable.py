#!/usr/bin/env python3
import json
import os

# 读取索引
with open('/data1/zzh/aesop/still_unsolvable.txt', 'r') as f:
    indices = [int(line.strip()) for line in f if line.strip().isdigit()]

# 读取题库
with open('/data1/zzh/verina/verina_lemmas_quickchecked.json', 'r') as f:
    data = json.load(f)

# 创建目录
os.makedirs('/data1/zzh/aesop/problems', exist_ok=True)

# 生成文件
for idx in indices:
    text = data[idx-1]["header"].replace("import Mathlib", "import Aesop") + "\n" + \
           data[idx-1]["lemma_formal_statements"].replace("sorry", "\n  aesop?\n  aesop?(config := { useDefaultSimpSet := false })")
    
    with open(f'/data1/zzh/aesop/problems/lemma_{idx}.lean', 'w') as f:
        f.write(text)

print(f"已生成 {len(indices)} 个 Lean 文件到 aesop/problems/")

