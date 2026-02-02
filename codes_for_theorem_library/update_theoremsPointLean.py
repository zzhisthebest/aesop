import os

# 1. 路径配置
# 你的 .lean 文件存放的物理文件夹
THEOREMS_DIR = "/data1/zzh/codetic/Codetic/theorems"
# 你的入口文件路径 (必须在 theorems 文件夹外层)
INDEX_FILE = "/data1/zzh/codetic/Codetic/theorems.lean"

def generate_theorems_index():
    if not os.path.exists(THEOREMS_DIR):
        print(f"❌ 错误: 找不到目录 {THEOREMS_DIR}")
        return

    # 2. 获取所有 .lean 文件名并排序 (保证编译顺序稳定)
    lean_files = sorted([
        f[:-5] for f in os.listdir(THEOREMS_DIR) 
        if f.endswith(".lean") and f != "theorems.lean"
    ])

    # 3. 写入内容
    with open(INDEX_FILE, "w", encoding="utf-8") as f:
        # 如果你开了 experimental.module，必须加这一行
        # 它的模块名应该是 Codetic.theorems
        f.write("module\n\n")
        
        f.write("/-\n自动化生成的汇总导入文件\n请勿手动修改此文件\n-/\n\n")
        
        if not lean_files:
            f.write("-- (目前该目录下没有 lean 文件)\n")
        else:
            for name in lean_files:
                # 模块路径必须是 库名.文件夹名.文件名
                f.write(f"import Codetic.theorems.{name}\n")
    
    print(f"✅ 成功更新 {INDEX_FILE}")
    print(f"📊 当前导入文件总数: {len(lean_files)}")

if __name__ == "__main__":
    generate_theorems_index()