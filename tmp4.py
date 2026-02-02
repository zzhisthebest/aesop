import re

# 输入与输出路径
log_path = '/data1/zzh/codetic/codes_for_theorem_library/failed_verified.txt'
output_path = 'referencers_list.txt'
target_id = "tmp_lemma_"

def main():
    # 存储结果的集合（自动去重）
    referencers = set()
    
    # 编译正则：匹配行首的 lemma_数字.lean
    # ^ 表示行首，(\d+) 捕获数字部分
    pattern = re.compile(r'^(lemma_\d+\.lean)')

    with open(log_path, 'r', encoding='utf-8') as f:
        for line in f:
            # 检查目标 ID 是否在这一行中
            if target_id in line:
                match = pattern.match(line)
                if match:
                    referencers.add(match.group(1))

    # 排序并写入文件
    sorted_refs = sorted(list(referencers), key=lambda x: int(re.search(r'\d+', x).group()))
    
    with open(output_path, 'w', encoding='utf-8') as f_out:
        for ref in sorted_refs:
            f_out.write(ref + '\n')

    print(f"✨ 任务完成！")
    print(f"📄 引用了 {target_id} 的题目已保存至: {output_path}")
    print(f"📊 总计数量: {len(sorted_refs)}")

if __name__ == "__main__":
    main()