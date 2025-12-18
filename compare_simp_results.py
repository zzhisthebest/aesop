#!/usr/bin/env python3
"""
对比使用和不使用默认 simp 定理集的 aesop 评估结果

用法：
    python compare_simp_results.py <file_without_default> <file_with_default> [output_file]
    
示例：
    python compare_simp_results.py \
        "/data1/zzh/verina/my_aesop (config := { useDefaultSimpSet := false })_eval_partial_results_on_16627.jsonl" \
        "/data1/zzh/verina/my_aesop_eval_partial_results_on_16627.jsonl" \
        "lost_problems.txt"
"""

import json
import sys

def compare_results(file1, file2, output_file=None):
    """对比两个结果文件"""
    results1 = []
    results2 = []
    
    with open(file1, 'r') as f:
        for line in f:
            if line.strip():
                results1.append(json.loads(line))
    
    with open(file2, 'r') as f:
        for line in f:
            if line.strip():
                results2.append(json.loads(line))
    
    if len(results1) != len(results2):
        print(f"警告: 两个文件的题目数量不一致 ({len(results1)} vs {len(results2)})")
    
    # 找出 file1 失败但 file2 成功的题目
    lost_indices = []
    
    for i in range(min(len(results1), len(results2))):
        proved1 = results1[i].get('is_valid_with_sorry', False)
        proved2 = results2[i].get('is_valid_with_sorry', False)
        
        if not proved1 and proved2:
            lost_indices.append(i + 1)
    
    # 统计
    proved1_count = sum(1 for r in results1 if r.get('is_valid_with_sorry', False))
    proved2_count = sum(1 for r in results2 if r.get('is_valid_with_sorry', False))
    
    # 打印统计
    print(f"文件1 (useDefaultSimpSet=false): {proved1_count}/{len(results1)} ({100*proved1_count/len(results1):.1f}%)")
    print(f"文件2 (默认配置): {proved2_count}/{len(results2)} ({100*proved2_count/len(results2):.1f}%)")
    print(f"损失题目数: {len(lost_indices)} ({100*len(lost_indices)/len(results1):.1f}%)")
    
    # 保存到文件
    if output_file:
        with open(output_file, 'w') as f:
            f.write("# 禁用默认 simp 定理集后失败的题目索引 (从1开始)\n")
            f.write("# useDefaultSimpSet=false 失败但默认配置成功的题目\n\n")
            f.write(f"总数: {len(lost_indices)}\n\n")
            f.write("索引列表:\n")
            for idx in lost_indices:
                f.write(f"{idx}\n")
        print(f"\n已保存到: {output_file}")
    else:
        print(f"\n损失的题目索引（前50个）: {lost_indices[:50]}")
        if len(lost_indices) > 50:
            print(f"... 还有 {len(lost_indices) - 50} 个")
    
    return lost_indices

if __name__ == "__main__":
    if len(sys.argv) < 3:
        print(__doc__)
        sys.exit(1)
    
    file1 = sys.argv[1]
    file2 = sys.argv[2]
    output_file = sys.argv[3] if len(sys.argv) > 3 else None
    
    compare_results(file1, file2, output_file)
