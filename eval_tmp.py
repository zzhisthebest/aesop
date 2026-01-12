import os
import subprocess
import argparse
from concurrent.futures import ProcessPoolExecutor, as_completed


THEOREMS_DIR = "/data1/zzh/aesop/Aesop/theorems"
IDS_TXT = "/data1/zzh/aesop/Aesop/theorems_ids.txt"


def clear_theorems_dir():
    if os.path.isdir(THEOREMS_DIR):
        for f in os.listdir(THEOREMS_DIR):
            path = os.path.join(THEOREMS_DIR, f)
            if os.path.isfile(path):
                os.remove(path)
    else:
        os.makedirs(THEOREMS_DIR, exist_ok=True)


def check_and_maybe_delete(file_path, do_delete: bool):
    filename = os.path.basename(file_path)

    try:
        result = subprocess.run(
            ['lake', 'env', 'lean', file_path],
            capture_output=True,
            text=True,
            timeout=300
        )

        # ✅ 通过
        if result.returncode == 0:
            if do_delete:
                os.remove(file_path)
            return filename, True

        # ❌ 不通过：写入 theorems
        target_path = os.path.join(THEOREMS_DIR, filename)

        with open(file_path, "r", encoding="utf-8") as f:
            content = f.read()

        content = (
            content
            .replace("theorem", "@[simp]\npublic theorem")
            .replace(
                "aesop(config:={enableGrind:=false,enableOmega:=false})",
                "sorry"
            )
            .replace("import Aesop", "import Lean")
        )

        with open(target_path, "w", encoding="utf-8") as f:
            f.write(content)

        stem, _ = os.path.splitext(filename)
        return stem, False

    except subprocess.TimeoutExpired:
        stem, _ = os.path.splitext(filename)
        return stem, False
    except Exception:
        stem, _ = os.path.splitext(filename)
        return stem, False


def parallel_clean(directory, max_workers=96, do_delete=False):
    if not os.path.isdir(directory):
        print(f"错误: 找不到目录 '{directory}'")
        return

    # ⭐ 启动前清空 theorems
    clear_theorems_dir()
    print(f"🧹 已清空: {THEOREMS_DIR}")

    lean_files = [
        os.path.abspath(os.path.join(directory, f))
        for f in os.listdir(directory)
        if f.endswith(".lean")
    ]

    if not lean_files:
        print(f"在 '{directory}' 中没有找到 .lean 文件。")
        return

    mode = "删除模式" if do_delete else "检查模式（不删除）"
    print(f"🚀 启动并行处理 | {mode}")
    print(f"进程数: {max_workers}")
    print(f"文件夹: {directory}")
    print(f"待处理文件总数: {len(lean_files)}\n")

    passed_count = 0
    failed_count = 0
    failed_ids = []

    with ProcessPoolExecutor(max_workers=max_workers) as executor:
        futures = {
            executor.submit(check_and_maybe_delete, f, do_delete): f
            for f in lean_files
        }

        for future in as_completed(futures):
            file_id, success = future.result()

            if success:
                passed_count += 1
                print(f"✅ 通过: {file_id}")
            else:
                failed_count += 1
                failed_ids.append(file_id)
                print(f"❌ 失败: {file_id}")

            total = passed_count + failed_count
            print(
                f"进度: {total}/{len(lean_files)} | "
                f"通过: {passed_count} | 失败: {failed_count}",
                end="\r"
            )

    print("\n\n✨ 任务完成！")
    print(f"✅ 通过: {passed_count}")
    print(f"⚠️ 失败: {failed_count}")

    with open(IDS_TXT, "w", encoding="utf-8") as f:
        for i in failed_ids:
            f.write(i + "\n")

    print(f"📄 失败编号已写入: {IDS_TXT}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="并行检查 Lean 文件，可选是否删除通过的文件"
    )
    parser.add_argument(
        "directory",
        nargs="?",
        default="/data1/zzh/aesop/problems2",
        help="包含 .lean 文件的目录"
    )
    parser.add_argument(
        "--delete",
        type=lambda x: x.lower() == "true",
        default=False,
        help="是否删除通过检查的 .lean 文件（true / false，默认 false）"
    )
    parser.add_argument(
        "--workers",
        type=int,
        default=96,
        help="并行进程数（默认 96）"
    )

    args = parser.parse_args()

    parallel_clean(
        args.directory,
        max_workers=args.workers,
        do_delete=args.delete
    )
