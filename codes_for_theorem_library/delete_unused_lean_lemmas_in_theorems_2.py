import os
import re

# 配置路径
log_path = '/data1/zzh/codetic/codes_for_theorem_library/passed_verified_1.txt'
library_dir = '/data1/zzh/codetic/theorems_copy' # 请确认这是你要删除文件所在的库目录

def cleanup_passed_theorems():
    if not os.path.exists(log_path):
        print(f"❌ 找不到日志文件: {log_path}")
        return

    # 1. 提取所有 SUCCESS 的文件名
    passed_filenames = []
    with open(log_path, 'r', encoding='utf-8') as f:
        for line in f:
            if "| SUCCESS |" in line:
                # 匹配行首的文件名，例如 lemma_123.lean
                match = re.match(r'^(lemma_\d+\.lean)', line)
                if match:
                    passed_filenames.append(match.group(1))

    if not passed_filenames:
        print("查无通过 (SUCCESS) 的记录。")
        return

    print(f"检测到 {len(passed_filenames)} 个已通过的题目，准备从库中删除...")

    # 2. 执行删除
    removed_count = 0
    for filename in passed_filenames:
        file_path = os.path.join(library_dir, filename)
        if os.path.exists(file_path):
            try:
                os.remove(file_path)
                removed_count += 1
            except Exception as e:
                print(f"无法删除 {filename}: {e}")
        else:
            # print(f"文件不存在，跳过: {filename}")
            pass

    print(f"\n✨ 清理完成！")
    print(f"✅ 已成功删除: {removed_count} 个文件")
    print(f"📂 目标目录: {library_dir}")

if __name__ == "__main__":
    cleanup_passed_theorems()