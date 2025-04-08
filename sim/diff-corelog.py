import argparse
import re

# Regular expression to match the DMEM line format, including operation (R/W) and 4-bit mask
# The first 0x<x8 hex digits> is the memory address (which can be 'z' or 'Z' as a wildcard)
# The second 0x<x8 hex digits> is the memory value (which must match exactly)
# The operation (R/W) and the 4-bit mask are captured
DMEM_PATTERN = re.compile(r"DMEM ([RW]) \((\S{4})\): 0x([0-9A-Fa-fzZ]{8}) 0x([0-9A-Fa-f]{8}) @\s+(\d+)")

def compare_files(vc_file, gl_file):
    try:
        with open(vc_file, 'r') as f1, open(gl_file, 'r') as f2:
            # Read lines from both files
            lines1 = f1.readlines()
            lines2 = f2.readlines()

            # Check if both files have the same number of lines
            if len(lines1) != len(lines2):
                print("Files have different number of lines.")
                return

            # Compare each line side by side
            for line_num, (line1, line2) in enumerate(zip(lines1, lines2), start=1):
                # Check if the lines match the DMEM pattern
                match1 = DMEM_PATTERN.match(line1)
                match2 = DMEM_PATTERN.match(line2)

                if match1 and match2:
                    # Extract operation (R/W), 4-bit mask, memory address, and value
                    op1, mask1, addr1, val1, time1 = match1.groups()
                    op2, mask2, addr2, val2, time2 = match2.groups()

                    # Check if the operation (R/W) is the same
                    if op1 != op2:
                        print(f"Line {line_num} differs (operation mismatch):")
                        print(f"vc_file: {line1.strip()}")
                        print(f"gl_file: {line2.strip()}")
                        print("-" * 40)
                        return  # Exit after the first mismatch

                    # Check if the 4-bit mask is the same
                    if mask1 != mask2:
                        print(f"Line {line_num} differs (mask mismatch):")
                        print(f"vc_file: {line1.strip()}")
                        print(f"gl_file: {line2.strip()}")
                        print("-" * 40)
                        return  # Exit after the first mismatch

                    # Create regex pattern for memory address, replacing 'z' or 'Z' with a wildcard for any hex digit
                    addr2_regex = ''.join(c if c not in 'zZ' else '[0-9A-Fa-f]' for c in addr2)

                    # Use regex to match addresses, treating z/Z as wildcards
                    if not re.match(f"^{addr2_regex}$", addr1):
                        # The addresses don't match (even after allowing 'z' or 'Z' to be wildcards)
                        print(f"Line {line_num} differs (address mismatch):")
                        print(f"vc_file: {line1.strip()}")
                        print(f"gl_file: {line2.strip()}")
                        print("-" * 40)
                        return  # Exit after the first mismatch

                    # Now check data match
                    if val1 != val2:
                        print(f"Line {line_num} differs (data mistmatch):")
                        print(f"vc_file: {line1.strip()}")
                        print(f"gl_file: {line2.strip()}")
                        print("-" * 40)
                        return  # Exit after the first mismatch

                    # Now check timestamps match
                    if time1 != time2:
                        print(f"Line {line_num} differs (timestamp mistmatch):")
                        print(f"vc_file: {line1.strip()}")
                        print(f"gl_file: {line2.strip()}")
                        print("-" * 40)
                        return  # Exit after the first mismatch

                else:
                    # If the lines do not match the expected pattern at all
                    if(line1 != line2):
                        print(f"Line {line_num} mismatch:")
                        print(f"vc_file: {line1.strip()}")
                        print(f"gl_file: {line2.strip()}")
                        print("-" * 40)
                        return  # Exit after the first mismatch

            # If no mismatches found
            print("No core log diffs")

    except FileNotFoundError as e:
        print(f"Error: {e.strerror} - {e.filename}")
    except Exception as e:
        print(f"An error occurred: {e}")

def main():
    # Set up argument parsing
    parser = argparse.ArgumentParser(description='Compare two text files line by line.')
    parser.add_argument('vc_file', help='Path to the vc_file (first file)')
    parser.add_argument('gl_file', help='Path to the gl_file (second file)')

    # Parse the command-line arguments
    args = parser.parse_args()

    # Call the comparison function with the provided filenames
    compare_files(args.vc_file, args.gl_file)

if __name__ == '__main__':
    main()
