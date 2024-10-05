import json
import os

def is_lemma_start(line):
    return line.strip().startswith(("Lemma", "Theorem", "Proposition", "Corollary"))

def is_lemma_end(line):
    return line.strip() == "Qed."

def process_coq_file(json_file, output_dir, adjacent_lemmas=[0, 10, 20]):
    with open(json_file, 'r') as f:
        data = json.load(f)

    code = data['code']
    theorems = data['theorems']

    os.makedirs(output_dir, exist_ok=True)

    # 生成完整的.v文件
    full_file_path = os.path.join(output_dir, "full_file.v")
    with open(full_file_path, 'w') as f:
        f.write('\n'.join(code))

    # 提取所有非lemma代码
    non_lemma_code = []
    in_lemma = False
    for line in code:
        if is_lemma_start(line):
            in_lemma = True
        elif is_lemma_end(line):
            in_lemma = False
        elif not in_lemma:
            non_lemma_code.append(line)

    # 为每个lemma生成独立的.v文件
    for n in adjacent_lemmas:
        lemma_dir = os.path.join(output_dir, f"lemmas_with_{n}_adjacent")
        os.makedirs(lemma_dir, exist_ok=True)

        for i, theorem in enumerate(theorems):
            lemma_name = theorem['name']
            lemma_begin = theorem['begin']
            lemma_end = theorem['end']

            # 创建lemma文件
            lemma_file_path = os.path.join(lemma_dir, f"{lemma_name}.v")
            with open(lemma_file_path, 'w') as f:
                # 写入所有非lemma代码
                f.write('\n'.join(non_lemma_code) + '\n\n')

                # 写入相邻的lemma（使用Admitted）
                start_index = max(0, i - n)
                end_index = min(len(theorems), i + n + 1)
                for adj_theorem in theorems[start_index:end_index]:
                    if adj_theorem != theorem:
                        adj_begin = adj_theorem['begin']
                        adj_end = adj_theorem['end']
                        f.write('\n'.join(code[adj_begin:adj_end-1]) + '\nAdmitted.\n\n')

                # 写入目标lemma的完整证明
                f.write('\n'.join(code[lemma_begin:lemma_end]) + '\n')

    return full_file_path, lemma_dir
# 使用函数
json_file_path = "/mnt/e/c++_files/PALM/data/weak-up-to/Applications.json"
output_directory = "/mnt/e/c++_files/PALM/process_sft_data/sft_data"

full_file, lemma_directories = process_coq_file(json_file_path, output_directory)

print(f"完整的.v文件已生成: {full_file}")
print("Lemma文件已生成在以下目录:")
for n in [0, 10, 20]:
    print(f"- 包含{n}个相邻lemma: {os.path.join(output_directory, f'lemmas_with_{n}_adjacent')}")