#!/usr/bin/env python3
import json
import os
import glob
from pathlib import Path

# 文件路径
jsonl_file = "/data1/zzh/verina/my_codetic_eval_partial_results_on_16627.jsonl"
json_file = "/data1/zzh/verina/verina_lemmas_quickchecked.json"
output_dir = "/data1/zzh/codetic/problems1"
os.makedirs(output_dir, exist_ok=True)
# 读取评估结果
print("Reading evaluation results...")
with open(jsonl_file, 'r') as f:
    results = [json.loads(line.strip()) for line in f]

# 读取题目
print("Reading problems...")
with open(json_file, 'r') as f:
    problems = json.load(f)

assert len(results) == len(problems), f"Mismatch: {len(results)} results vs {len(problems)} problems"

print(f"Total problems: {len(problems)}")

# 获取失败的题目索引
failed_indices = []
for i, result in enumerate(results):
    # 如果 is_valid_no_sorry 为 False，说明没有证明成功
    if not result.get("is_valid_no_sorry", True):
        failed_indices.append(i)

print(f"Failed problems: {len(failed_indices)}")

# # 获取 problems1 目录中已有的问题编号
# existing_numbers = set()
# for f in os.listdir(output_dir):
#     if f.startswith('lemma_') and f.endswith('.lean') and not f.endswith('_newcodetic.lean'):
        
#         # 提取数字部分，例如 lemma_123.lean -> 123, lemma_123_studied.lean -> 123
#         parts = f.replace('lemma_', '').replace('.lean', '').split('_')
#         num_part = parts[0]
#         if num_part.isdigit():
#             existing_numbers.add(int(num_part))

# print(f"Existing problem numbers in problems1: {len(existing_numbers)}")

# 处理失败的题目
copied_count = 0
skipped_count = 0

for idx in failed_indices:
    # 使用题目在 JSON 中的索引作为编号
    problem_num = idx+1
    
    # # 检查是否已存在
    # if problem_num in existing_numbers:
    #     skipped_count += 1
    #     continue
    
    problem = problems[idx]
    
    # 创建文件内容
    header = problem.get('header', '')
    header=header.replace('import Mathlib', 'import Codetic')
    statements = problem.get('lemma_formal_statements', '')
    statements=statements.replace('sorry', '\n  codetic?')
    content = header + '\n' + statements
    
    # 写入文件
    target_file = os.path.join(output_dir, f"lemma_{problem_num}_newcodetic.lean")
    
    try:
        with open(target_file, 'w') as tf:
            tf.write(content)
        
        copied_count += 1
        if copied_count % 100 == 0:
            print(f"  Processed {copied_count} problems...")
    except Exception as e:
        print(f"Error writing {target_file}: {e}")

print(f"\nSummary:")
print(f"  Total failed: {len(failed_indices)}")
print(f"  Copied: {copied_count}")
print(f"  Skipped (already exists): {skipped_count}")
print(f"\nFiles are named as: lemma_<index>_newcodetic.lean")
print(f"  where <index> is the position in verina_lemmas_quickchecked.json (0-based)")

