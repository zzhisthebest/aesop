import json
import os
import shutil

def load_solved_ids(path):
    """读取 solved_ids.txt，返回一个 int 集合"""
    with open(path, "r", encoding="utf-8") as f:
        return {int(line.strip()) for line in f if line.strip().isdigit()}

def main():
    json_file = "/data1/zzh/verina/verina_lemmas_quickchecked.json"
    solved_ids_file = "solved_ids.txt"

    tactic = "aesop"
    # tactic = "aesop"
    import_statement = "import Aesop\n"

    # 读取 solved ids
    solved_ids = load_solved_ids(solved_ids_file)
    print(f"Loaded {len(solved_ids)} solved ids")

    with open(json_file, 'r', encoding='utf-8') as f:
        data = json.load(f)

    if not data:
        print("Error: JSON file is empty")
        return

    print(f"Processing {len(data)} objects from {json_file}")

    # 输出目录
    output_path = "/data1/zzh/aesop/problems1"
    if os.path.exists(output_path):
        shutil.rmtree(output_path)
        print(f"Cleared existing directory: {output_path}")
    os.makedirs(output_path)

    written = 0

    # 只处理编号在 solved_ids 中的题目
    for i, obj in enumerate(data):
        if i in solved_ids:
            continue

        obj["header"] = obj["header"].replace("import Mathlib\n", "")
        proof_content = (
            import_statement
            + obj["header"]
            + "\n"
            + obj["lemma_formal_statements"].replace("sorry", f"\n{tactic}")
        )

        file_name = f"lemma_{i}.lean"
        full_path = os.path.join(output_path, file_name)

        with open(full_path, 'w', encoding='utf-8') as f_out:
            f_out.write(proof_content)

        written += 1

    print(f"Finished: wrote {written} files to {output_path}")

if __name__ == "__main__":
    main()
