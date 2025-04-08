module top_tb;

    timeunit 1ns;
    timeprecision 1ns;

    bit clk;
    initial clk = 1'b1;
    always #1 clk = ~clk;

    bit rst;

    int timeout = 10000000; // In cycles, change according to your needs

    logic [15:0]  rand_key, rand_mod_n, rand_msg;
    logic [15:0]  output_msg;
    logic [800000:0] golden_msg;
    logic         output_flag, start_flag;


    `include "RSA_randinst.svh"
    RandInst gen = new();

    RSA_ACCELERATOR dut(
        .clk           (clk),
        .rst_n         (rst),
        .RSA_start     (start_flag),
        .RSA_key       (rand_key),
        .mod_n         (rand_mod_n),
        .msg_block     (rand_msg),
        .output_msg    (output_msg),
        .idle_flag     (output_flag)
    );

    task calc_golden_msg(input [15:0] golden_key, golden_message, golden_mod_n);

    logic [15:0] e, result, cmp_msg;
    logic [31:0] intermediate_res, intermediate_mes;

    e       = golden_key;
    result  = 1'b1;
    cmp_msg = golden_message;

    while(e != '0) begin
        
        if(e[0] == 1'b1) begin
            intermediate_res = result * cmp_msg;
            result           = intermediate_res % golden_mod_n;
        end

        intermediate_mes = cmp_msg * cmp_msg;
        cmp_msg          = intermediate_mes % golden_mod_n;

        e = e >> 1;
        
    end

    @(posedge clk);

    golden_msg <= result;

    endtask

    task run_random_inputs();
        @(posedge clk);

        // Always read out a valid instruction.
        if (output_flag) begin
            if(golden_msg != output_msg) begin
                $error("TB Error: Value Mismatch");
                $finish;
            end 

            if(golden_msg == output_msg) begin
                $display("value match: success");
            end

            // @(posedge clk);
            gen.randomize();
            rand_key   <= gen.rand_key;
            // gen.randomize();
            rand_mod_n <= gen.rand_modN;
            // gen.randomize();
            rand_msg   <= gen.rand_msg;
            start_flag <= 1'b1;
            @(posedge clk);
            start_flag <= 1'b0;

            calc_golden_msg(rand_key, rand_msg, rand_mod_n);
             
        end

    

    endtask : run_random_inputs


    initial begin
        $fsdbDumpfile("dump.fsdb");
        $fsdbDumpvars(0, "+all");
        rst = 1'b0;
        repeat (5) @(posedge clk);
        rst = 1'b1;
    end

    always @(posedge clk) begin
        
        if (timeout == 0) begin
            $display("All Values passed");
            $finish;
        end

        run_random_inputs();

        timeout <= timeout - 1;
        // $display(timeout);
    end

endmodule : top_tb
