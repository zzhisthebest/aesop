#!/usr/bin/env python3
import json
import subprocess
from multiprocessing import Pool
from tqdm import tqdm

def test_problem(args):
    idx, data_item = args
    code = data_item["header"].replace("import Mathlib", "import Aesop") + "\n" + \
           data_item["lemma_formal_statements"].replace("sorry", "\n  aesop (config := { useDefaultSimpSet := false })")
    
    # 写临时文件
    tmp_file = f'/tmp/test_{idx}.lean'
    with open(tmp_file, 'w') as f:
        f.write(code)
    
    # 运行
    try:
        result = subprocess.run(
            ['lake', 'env', 'lean', tmp_file],
            cwd='/data1/zzh/aesop',
            capture_output=True,
            timeout=60
        )
        return (idx, result.returncode == 0)
    except subprocess.TimeoutExpired:
        return (idx, False)

# 读取题目索引
with open('/data1/zzh/aesop/still_unsolvable.txt', 'r') as f:
    indices = [int(line.strip()) for line in f if line.strip().isdigit()]

# 读取题库
with open('/data1/zzh/verina/verina_lemmas_quickchecked.json', 'r') as f:
    data = json.load(f)

# 准备任务
tasks = [(idx, data[idx-1]) for idx in indices]

# 并行测试
with Pool(64) as pool:
    results = list(tqdm(pool.imap(test_problem, tasks), total=len(tasks)))

# 筛选无法证明的
unsolvable = [idx for idx, success in results if not success]

# 保存结果
with open('/data1/zzh/aesop/still_unsolvable.txt', 'w') as f:
    f.write(f"# 使用 aesop (config := {{ useDefaultSimpSet := false }}) 仍无法证明的题目\n\n")
    f.write(f"总数: {len(unsolvable)}\n\n")
    for idx in unsolvable:
        f.write(f"{idx}\n")

print(f"\n原有 {len(indices)} 题，现在还有 {len(unsolvable)} 题无法证明")
print(f"成功解决了 {len(indices) - len(unsolvable)} 题")

