set_option incdir $env(DW_INC)

read_file -type verilog $env(PKG_SRCS) $env(RTL_SRCS) $env(DW_IP)

read_file -type awl lint.awl

set_option top $env(LINT_TOP)
set_option enable_gateslib_autocompile yes
set_option language_mode verilog
set_option enableSV09 yes
set_option enable_save_restore no
set_option mthresh 2000000000
set_option sgsyn_loop_limit 2000000000

set_option mthresh 65536

current_goal Design_Read -top $env(LINT_TOP)

current_goal lint/lint_turbo_rtl -top $env(LINT_TOP)

set_parameter checkfullstruct true

# Waivers
waive -rules {W240} -file {"/software/Synopsys-2021_x86_64/syn/R-2020.09-SP4/dw/sim_ver/DW_div_seq.v"}
waive -rules {W240} -file {"/software/Synopsys-2021_x86_64/syn/R-2020.09-SP4/dw/sim_ver/DW_mult_seq.v"}

run_goal