module qspi_stub(
    inout   wire    [3:0]           qspi_io,
    input   logic                   qspi_io_t,
    input   wire                    qspi_ck,
    input   wire                    qspi_cs
);

    logic   [7:0]           mem [2**24];
    logic   [3:0]           qspi_io_logic;
    
    genvar n;
    generate
        for (n=0; n<4; n++) begin
            bufif1 qspi_io_buf_(qspi_io[n], qspi_io_logic[n], qspi_io_t); 
        end
    endgenerate
    
    initial
    begin
        automatic string memfile = {getenv("ECE411_MEMLST"), "_1.lst"};
        $readmemh(memfile, mem);
    end

    always begin
        automatic bit [7:0] cmd;
        automatic bit [23:0] addr;
        automatic bit [7:0] mode;
        @(negedge qspi_cs);
        for (int i = 7; i >= 0; i--) begin
            @(posedge qspi_ck);
            cmd[i] = ~qspi_io_t ? qspi_io[0] : 1'bx;
        end
        assert (cmd == 8'hEB) else begin
            $display("ERROR: qspi wrong cmd, expected: %h, detected: %h, time: %0t", 8'hEB, cmd, $time);
            #1
            $finish;
        end
        for (int i = 5; i >= 0; i--) begin
            @(posedge qspi_ck);
            for (int j = 0; j < 4; j++) begin
                addr[i*4+j] = ~qspi_io_t ? qspi_io[j] : 1'bx;
            end
        end
        // $display("INFO: qspi read addr: %h, data: %h, time: %0t", addr, {mem[addr+3], mem[addr+2], mem[addr+1], mem[addr]} ,$time);
        for (int i = 1; i >= 0; i--) begin
            @(posedge qspi_ck);
            for (int j = 0; j < 4; j++) begin
                mode[i*4+j] = ~qspi_io_t ? qspi_io[j] : 1'bx;
            end
        end
        assert (mode[7:4] == 4'hF) else begin
            $display("ERROR: qspi wrong mode, expected: %h, detected: %h, time: %0t", 8'b1111xxxx, mode, $time);
            #1
            $finish;
        end
        for (int i = 0; i < 4; i++) begin
            @(posedge qspi_ck);
        end
        for (int i = 0; i < 16; i++) begin
            @(negedge qspi_ck);
            if (i % 2 == 0) begin
                qspi_io_logic = mem[addr][7:4];
            end else begin
                qspi_io_logic = mem[addr][3:0];
                addr += 24'd1;
            end
        end
        @(posedge qspi_cs);
    end

endmodule

