import random
import os

# Parameters
num_cores = 4  # Number of CPU cores
num_transactions = 2000  # Number of transactions per core
data_width = 8  # Data width in bits
address_space_width = 6  # Address width in bits
idle_cycles = 5  # Number of idle cycles to append

# Transaction types
TRANSACTION_TYPES = ["Read", "Write", "Idle"]

# Generate direct test vectors
def generate_directed_transaction(core):
    test_vector = []

    for i in range(4):
        test_vector.append("0 0 0")
        if (core == i):
          test_vector.append("1 0 4")

        for i in range(100):
          test_vector.append("2 0 0")

        test_vector.append("0 1 0")
        if (core == i):
          test_vector.append("1 1 4")

        for i in range(100):
          test_vector.append("2 0 0")

        test_vector.append("0 2 0")
        if (core == i):
          test_vector.append("1 2 4")

        for i in range(100):
          test_vector.append("2 0 0")

        test_vector.append("0 3 0")
        if (core == i):
          test_vector.append("1 3 4")

        for i in range(100):
          test_vector.append("2 0 0")

     
    return test_vector

# Generate random test vectors
def generate_random_transaction():
    trans_type = random.choice(TRANSACTION_TYPES)
    addr = random.randint(0, (2**address_space_width) - 1)
    wdata = random.randint(0, (2**data_width) - 1)
    
    if trans_type == "Read":
        return f"0 {addr} 0"
    elif trans_type == "Write":
        return f"1 {addr} {wdata}"
    else:
        return f"2 0 0"

# Create output directory
def write_test_vectors():
    for core in range(num_cores):
        core_file = f"inputs_{core}.txt"
        parent_file = f"../inputs_{core}.txt"

        # Generate directed transactions
        transactions = generate_directed_transaction(core)
        
        # Generate random transactions
        transactions.extend([generate_random_transaction() for _ in range(num_transactions)])

         # Append idle cycles at the end
        transactions.extend([f"2 0 0" for _ in range(idle_cycles)])
        
        # Write to both current and parent directory
        for file in [core_file, parent_file]:
            with open(file, "w") as f:
                f.write("\n".join(transactions))
                print(f"Generated {file}")

# Run the script
if __name__ == "__main__":
    os.makedirs("..", exist_ok=True)  # Ensure parent directory exists
    write_test_vectors()
    print(f"Generated {num_cores} core test vector files with {num_transactions} transactions each.")
