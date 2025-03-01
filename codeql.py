import json
from collections import defaultdict


# 读取文件并统计数据
def process_file(file_path):
    result = defaultdict(list)  # 使用 defaultdict 自动初始化列表

    with open(file_path, "r") as file:
        for line in file:
            # 去除换行符并分割为 A 和 B
            data = line.strip().split(",")
            result[data[1]].append(data[3].strip())  # 将 B 添加到 A 对应的列表中

    return result


def filter_data(data):
    return {key: value for key, value in data.items() if len(value) > 1}


# 将统计结果保存为 JSON 文件
def save_to_json(data, output_path):
    with open(output_path, "w") as json_file:
        json.dump(data, json_file, indent=4)  # 使用 indent 格式化 JSON 文件


# 主函数
def main():
    input_file = "codeql.csv"  # 输入文件路径
    output_file = "codeql.json"  # 输出文件路径

    # 处理文件并保存结果
    data = process_file(input_file)
    filtered_data = filter_data(data)
    save_to_json(filtered_data, output_file)

    print(f"结果已保存到 {output_file}")


if __name__ == "__main__":
    main()
