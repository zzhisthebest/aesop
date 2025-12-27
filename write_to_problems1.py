import json
import os
import shutil
def main():
    json_file = "/data1/zzh/verina/verina_lemmas_quickchecked.json"
    tactic="aesop"
    # tactic="aesop"
    import_statement = "import Aesop\n"
    with open(json_file, 'r', encoding='utf-8') as f:
        data = json.load(f)
    
    if not data:
        print("Error: JSON file is empty")
        return
    
    print(f"Processing {len(data)} objects from {json_file}")
    
    # Prepare all proofs with tactic based on premise_names
    all_proofs = []
    for obj in data:
        obj["header"]=obj["header"].replace("import Mathlib\n", "")
        test_code = import_statement+obj["header"]+"\n"+obj["lemma_formal_statements"].replace("sorry", f"\n{tactic}")
        all_proofs.append(test_code)
    # 1. 定义并创建输出目录
    output_path = "/data1/zzh/aesop/problems1"
    #  如果文件夹存在，直接删除整个文件夹及其内容
    if os.path.exists(output_path):
        shutil.rmtree(output_path)
        print(f"Cleared existing directory: {output_path}")

    # 2. 重新创建空的文件夹
    os.makedirs(output_path)

    # 2. 启动新循环进行文件写入
    for i, proof_content in enumerate(all_proofs):
        file_name = f"lemma_{i}.lean"
        full_path = os.path.join(output_path, file_name)
        
        with open(full_path, 'w', encoding='utf-8') as f_out:
            f_out.write(proof_content)
            
    print(f"Finished: {len(all_proofs)} files saved to {output_path}")

if __name__ == "__main__":
    main()