import json
import os
import re

# 路径配置
JSON_FILE = "/data1/zzh/verina/verina_lemmas_quickchecked.json"
IDS_TXT = "/data1/zzh/codetic/theorems_ids.txt"
DST_DIR = "/data1/zzh/codetic/theorems_copy"

def load_target_ids(path):
    """读取 IDs 文件，支持 'lemma_123' 或 '123' 格式，返回整数集合"""
    target_ids = set()
    if not os.path.exists(path):
        return target_ids
    with open(path, "r", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line: continue
            # 提取数字部分，兼容 'lemma_123' 或直接 '123'
            match = re.search(r'(\d+)', line)
            if match:
                target_ids.add(int(match.group(1)))
    return target_ids

def main():
    # 1. 准备工作
    if not os.path.isfile(JSON_FILE):
        print(f"❌ 找不到 JSON 文件: {JSON_FILE}")
        return
    
    os.makedirs(DST_DIR, exist_ok=True)
    target_ids = load_target_ids(IDS_TXT)
    print(f"🚀 已加载目标 ID 数量: {len(target_ids)}")

    with open(JSON_FILE, 'r', encoding='utf-8') as f:
        data = json.load(f)

    written = 0
    
    # 2. 遍历 JSON 数据
    # enumerate(data) 这里的 i 对应 lemma_i 的编号
    for i, obj in enumerate(data):
        if i not in target_ids:
            continue

        # 获取原始内容
        # 假设 JSON 中 header 包含 import，lemma_formal_statements 包含定义和证明
        header = obj.get("header", "").replace("import Mathlib\n", "import Codetic\n")
        body = obj.get("lemma_formal_statements", "")

        # 拼接并处理内容
        content = header + "\n" + body 
        content=content.replace("sorry","\nsorry")
        
        # --- 写入文件 ---
        file_name = f"lemma_{i}.lean"
        dst_path = os.path.join(DST_DIR, file_name)
        
        with open(dst_path, "w", encoding="utf-8") as f:
            f.write(content)
        
        written += 1

    print(f"\n✨ 处理完成")
    print(f"✅ 成功从 JSON 提取并写入: {written} 个文件")
    print(f"📂 目标目录: {DST_DIR}")

if __name__ == "__main__":
    main()