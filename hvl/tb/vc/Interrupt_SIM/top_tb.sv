module top_tb
#(
 //# of intterupt connections
    parameter  INTERRUPT_LINES = 16,
    parameter  INTERRUPT_BITS  = $clog2(INTERRUPT_LINES) 
);

    timeunit 1ns;
    timeprecision 1ns;

    bit clk;
    initial clk = 1'b1;
    always #1 clk = ~clk;

    bit rst;

    int timeout = 100; // In repeats, change according to your needs

    //EXTERNAL DEVICE SIDE CONNECTIONS
    logic [INTERRUPT_LINES-1:0] Interrupt_ID;
    logic                       in_service;
    //CORE SIDE CONNECTIONS
    //intialize/populate signals
    logic                       read_mask;
    logic                       update_int_mask;
    logic [INTERRUPT_LINES-1:0] wdata_int_mask;
    logic [INTERRUPT_LINES-1:0] int_mask_val;
    logic [INTERRUPT_LINES-1:0] intermediate_result;

    logic                      read_vec_table;
    logic [INTERRUPT_BITS-1:0] table_entry_id;
    logic [31:0]               wdata_vec_table;
    logic                      update_int_vec_table;
    logic                      int_vec_table_pc;

    //service/signal interrupt signals
    logic                      interupt_serviced;
    logic [31:0]               interrupt_PC;
    logic                      signal_interrupt;

    logic      [31:0]          Gold_Vector_Table [INTERRUPT_LINES];


    `include "Interrupt_randinst.svh"
    int clk_delay;
    logic [INTERRUPT_LINES-1:0] i;

    RandInitPic gen_init = new();
    RandSingInt gen = new();

    task init_entry_interrupt_vect_table();
        gen_init.randomize(rand_entry_data, rand_entry_id);
        gen_init.init_cg.sample();

        table_entry_id   <= gen_init.rand_entry_id;
        wdata_vec_table  <= gen_init.rand_entry_data;
        read_mask        <=1'b1;
        read_vec_table   <=1'b1;
        repeat (1) @(posedge clk);

        intermediate_result = (16'h0001 << table_entry_id);
        wdata_int_mask <= (int_mask_val | intermediate_result);
        // case(table_entry_id)
        //     4'd0: begin
               
        //     end
        //     4'd1: begin
        //         wdata_int_mask <=int_mask_val | 16'h0002;
        //     end
        //     4'd2: begin
        //         wdata_int_mask <=int_mask_val | 16'h0004;
        //     end
        //     4'd3: begin
        //         $display("testing d3");
        //         wdata_int_mask <=(int_mask_val | 16'h0008);
        //         $finish;
        //     end
        //     4'd4: begin
        //         wdata_int_mask <=int_mask_val | 16'h0010;
        //     end
        //     4'd5: begin
        //         wdata_int_mask <=int_mask_val | 16'h0020;
        //     end
        //     4'd6: begin
        //          wdata_int_mask <=int_mask_val | 16'h0040;
        //     end
        //     4'd7: begin
        //         wdata_int_mask <=int_mask_val | 16'h0080;
        //     end
        //     4'd8: begin
        //         wdata_int_mask <=int_mask_val | 16'h0100;
        //     end
        //     4'd9: begin
        //         wdata_int_mask <=int_mask_val | 16'h0200;
        //     end
        //     4'd10: begin
        //         wdata_int_mask <=int_mask_val | 16'h0400;
        //     end
        //     4'd11: begin
        //         wdata_int_mask <=int_mask_val | 16'h0800;
        //     end
        //     4'd12: begin
        //         wdata_int_mask <=int_mask_val | 16'h1000;
        //     end
        //     4'd13: begin
        //         wdata_int_mask <=int_mask_val | 16'h2000;
        //     end
        //     4'd14: begin
        //         wdata_int_mask <= int_mask_val | 16'h4000;
        //     end
        //     4'd15: begin
        //         wdata_int_mask <= int_mask_val | 16'h8000;
        //     end
        // endcase

        update_int_vec_table <= 1'b1;

        repeat (1) @(posedge clk);

        read_mask            <= 1'b0;
        read_vec_table       <= 1'b0;
        update_int_vec_table <= 1'b0;
        update_int_mask      <= 1'b1;

        Gold_Vector_Table[gen_init.rand_entry_id] <= gen_init.rand_entry_data;
        repeat (1) @(posedge clk);

        update_int_mask      <= 1'b0;
    endtask : init_entry_interrupt_vect_table

    //Run task to test RSA_accelerator with random inputs/use assertions to compare outputs
    task signal_random_interrupts();

        if(!signal_interrupt) begin
            gen_init.randomize(rand_Interrupt_ID);
            Interrupt_ID <= gen_init.rand_Interrupt_ID;

            repeat (1) @(posedge clk);
            Interrupt_ID <= '0;
            gen_init.latched_Interrupt_ID = dut.latch_interrupt;

            clk_delay = $urandom_range(5,20);
            repeat (clk_delay) @(posedge clk);
        end else begin  
            Interrupt_ID <= '0;
            repeat (1) @(posedge clk);
        end
    endtask : signal_random_interrupts

    task signal_random_single_interrupts();

        if(!in_service) begin
            gen.randomize(rand_single_Interrupt_ID);
            Interrupt_ID <= gen.rand_single_Interrupt_ID;
            // gen.single_int.sample();

            repeat (1) @(posedge clk);
            Interrupt_ID <= '0;
            
            clk_delay = $urandom_range(5,20);
            repeat (clk_delay) @(posedge clk);

        end else begin  
            Interrupt_ID <= '0;
            repeat (1) @(posedge clk);

        end
    endtask : signal_random_single_interrupts


    interrupt_controller dut(
        .clk(clk), 
        .rst(rst),

        .interrupt_id(Interrupt_ID), 
        .in_service(in_service),

        .read_mask(read_mask), 
        .update_int_mask(update_int_mask),
        .wdata_int_mask(wdata_int_mask),
        .int_mask_val(int_mask_val),

        .read_vec_table(read_vec_table),
        .table_entry_id(table_entry_id),
        .wdata_vec_table(wdata_vec_table),
        .update_int_vec_table(update_int_vec_table),
        .int_vec_table_pc(int_vec_read_pc),

        .interrupt_serviced(interupt_serviced),
        .interrupt_PC(interrupt_PC),
        .signal_interrupt(signal_interrupt)
    );


    initial begin

        gen.single_int_range.constraint_mode(0);

        if (~gen.single_int_range.constraint_mode())
            $display("constraint off");
        else 
            $display("constraint on");

        // $finish;

        $fsdbDumpfile("dump.fsdb");
        $fsdbDumpvars(0, "+all");

        gen_init.latched_Interrupt_ID = '0;
        interupt_serviced <= 1'b0;
        rst = 1'b1;
        repeat (5) @(posedge clk);
        rst = 1'b0;

        // init_pic         = 1'b0;
        Interrupt_ID     = '0;
        table_entry_id   = '0;
        wdata_vec_table  = '0;
        wdata_int_mask   = '0;

        repeat (1) @(posedge clk);
        $display("start intialize");
        repeat (1) @(posedge clk);

        repeat($urandom_range(64,128)) begin
            repeat (1) @(posedge clk);
            init_entry_interrupt_vect_table();
        end

        repeat (1) @(posedge clk);

        $display("end intialize");

        fork //CPU thread to randomly send back interrupt serviced request if interrupt started
            forever begin
            repeat(1) @(posedge clk);

                if(signal_interrupt) begin
                    repeat ($urandom_range(10,50)) @(posedge clk);
                    interupt_serviced <= 1'b1;
                    repeat(1) @(posedge clk);
                    interupt_serviced <= 1'b0;
                end
            end
        join_none

        fork //sampling thread to cover internal interrupt signals
            forever begin
                // $display("fork2");
                if(signal_interrupt) begin
                    gen.signaled_single_Interrupt_ID = dut.signal_int_id;
                    gen.single_int.sample();
                    // $display("succesful sample");
                end
                repeat(1) @(posedge clk);
            end
        join_none

        repeat (timeout) begin
            repeat (1) @(posedge clk);

            fork //CPU thread to randomly send back interrupt serviced request if interrupt started
                forever begin
                repeat(1) @(posedge clk);

                    if(signal_interrupt) begin
                        repeat ($urandom_range(10,50)) @(posedge clk);
                        interupt_serviced <= 1'b1;
                        repeat(1) @(posedge clk);
                        interupt_serviced <= 1'b0;
                    end
                end
            join_none
            
            fork //sampling thread to cover internal interrupt signals
                forever begin
                    repeat(1) @(posedge clk);
                    if(signal_interrupt) begin
                        gen_init.signaled_Interrupt_ID = dut.signal_int_id;
                        gen_init.internal_int.sample();
                    end
                end
            join_none

            signal_random_interrupts();
        end 

        timeout = 1000;
        i       = '1;
        // gen.rand_single_Interrupt_ID    = '0;
        // gen.rand_single_Interrupt_ID[0] = 1'b1;


        gen.single_int_range.constraint_mode(1);

        repeat (timeout) begin
            repeat (1) @(posedge clk);
            signal_random_single_interrupts();

            fork //CPU thread to randomly send back interrupt serviced request if interrupt started
                forever begin
                repeat(1) @(posedge clk);

                    if(signal_interrupt) begin
                        repeat ($urandom_range(10,50)) @(posedge clk);
                        interupt_serviced <= 1'b1;
                        repeat(1) @(posedge clk);
                        interupt_serviced <= 1'b0;
                    end
                end
            join_none

            fork //sampling thread to cover internal interrupt signals
                forever begin
                    repeat(1) @(posedge clk);
                    if(signal_interrupt) begin
                        gen.signaled_single_Interrupt_ID = dut.signal_int_id;
                        gen.single_int.sample();
                    end
                end
            join_none
        end

        timeout = 500;

        repeat (timeout) begin

            if(!in_service) begin
                Interrupt_ID <= i;
                // gen.single_int.sample();

                repeat (1) @(posedge clk);
                Interrupt_ID <= '0;
                i = i<<1;

                clk_delay = $urandom_range(5,20);
                repeat (clk_delay) @(posedge clk);
            end else begin  
                Interrupt_ID <= '0;
                repeat (1) @(posedge clk);
            end

            
        end

        $display("All Values passed");
        $finish;
    end


endmodule : top_tb
