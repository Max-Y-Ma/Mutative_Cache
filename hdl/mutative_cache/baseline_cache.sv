module mutative_cache
import mutative_types::*;
(
    input   logic           clk,
    input   logic           rst,

    // cpu side signals, ufp -> upward facing port
    input   logic   [31:0]  ufp_addr,      //cpu cache addr (from)
    input   logic   [3:0]   ufp_rmask,     //cpu read signal (from)
    input   logic   [3:0]   ufp_wmask,     //cpu write signal (from)
    output  logic   [31:0]  ufp_rdata,     //cache read data
    input   logic   [31:0]  ufp_wdata,     //cpu write data (from)
    output  logic           ufp_resp,      //cache response

    // memory side signals, dfp -> downward facing port
    output  logic   [31:0]  dfp_addr, //cache/mem addr
    output  logic           dfp_read, //main mem read signal
    output  logic           dfp_write, //main mem write signal
    input   logic   [255:0] dfp_rdata, //main mem read data (from)
    output  logic   [255:0] dfp_wdata, //main mem write data
    input   logic           dfp_resp //main mem response (from)
);

    logic   [31:0]  ufp_addr_ff;
    logic   [3:0]   ufp_rmask_ff;
    logic   [3:0]   ufp_wmask_ff;
    logic   [31:0]  ufp_wdata_ff;
    logic           idle;

    logic   tag_array_csb0         [WAYS-1:0];
    logic   data_array_csb0        [WAYS-1:0];
    logic   valid_array_csb0       [WAYS-1:0];
    logic   flush_tag_array_csb0   [WAYS-1:0];
    logic   flush_data_array_csb0  [WAYS-1:0];
    logic   flush_valid_array_csb0 [WAYS-1:0];
    logic   real_tag_array_csb0    [WAYS-1:0];
    logic   real_data_array_csb0   [WAYS-1:0];
    logic   real_valid_array_csb0  [WAYS-1:0];
    logic   true_csb0              [WAYS-1:0];
    logic   real_web               [WAYS-1:0];

    logic [SET_BITS-1:0] real_set_addr [WAYS-1:0];

    //cache addr = 32 bits = 23 bits for tag, 4 bits for set (16 sets), 5 bits for blk offset
    logic                      cpu_request;
    logic                      hit;
    logic                      wb_en;
    logic                      write_from_cpu;
    logic [1:0]                setup; //0: DM, 1: 2-WAY, 2: 4-WAY, 3: 8-WAY
    logic                      cache_wen;
    logic                      dirty_en;
    cache_output_t             cache_output [WAYS];
    cache_address_t            cache_address;
    logic                      mem_write_cache;
    logic [31:0]               cache_data_wmask;
    logic [255:0]              cache_wdata;
    logic [WAY_IDX_BITS-1:0]   hit_way;
    logic [WAYS-1:0]           evict_we;
    logic [WAY_IDX_BITS-1:0]   evict_way;
    logic [WAYS-1:0]           way_we;


    logic [WAYS-1:0]           valid_vector;
    logic [WAYS-1:0]           dirty_vector;
    logic [TAG_BITS-1:0]       dirty_tag_vector [WAYS];
    logic [CACHELINE_SIZE-1:0] dirty_data_vector [WAYS];

    logic [SET_BITS:0]         flush_set_addr;
    logic [255:0]              flush_dfp_wdata;
    logic                      flush_dfp_write;
    logic [31:0]               flush_dfp_addr;
    logic                      setup_ready;
    logic                      setup_valid;
    logic                      setup_update;
    logic                      flush_stall;

    always_comb begin
        cpu_request = '0;
        cache_address = '0;

        if (idle && ~flush_stall) begin
            cpu_request = |ufp_rmask || |ufp_wmask;
            cache_address = ufp_addr;
        end
        else begin
            cpu_request = |ufp_rmask_ff || |ufp_wmask_ff;
            cache_address = ufp_addr_ff;
        end
    end

    always_ff @(posedge clk) begin
        if(rst) begin
            ufp_addr_ff <= '0;
            ufp_rmask_ff <= '0;
            ufp_wmask_ff <= '0;
            ufp_wdata_ff <= '0;
        end
        else if (flush_stall && (|ufp_rmask || |ufp_wmask)) begin
            ufp_addr_ff  <= ufp_addr;
            ufp_rmask_ff <= ufp_rmask;
            ufp_wmask_ff <= ufp_wmask;
            ufp_wdata_ff <= ufp_wdata;
        end
        else if (idle && ~flush_stall) begin
            ufp_addr_ff  <= ufp_addr;
            ufp_rmask_ff <= ufp_rmask;
            ufp_wmask_ff <= ufp_wmask;
            ufp_wdata_ff <= ufp_wdata;
        end
    end

    always_comb begin
        real_tag_array_csb0   = '{default: '1};
        real_data_array_csb0  = '{default: '1};
        real_valid_array_csb0 = '{default: '1};
        real_web              = '{default: '1};
        real_set_addr         = '{default: '0};

        for (int i = 0; i < WAYS; i++) begin
            real_tag_array_csb0[i] = tag_array_csb0[i] | true_csb0[i];
            real_data_array_csb0[i] = data_array_csb0[i] | true_csb0[i];
            real_valid_array_csb0[i] = valid_array_csb0[i] | true_csb0[i];
            real_web[i] = ~(way_we[i] & cache_wen);
            real_set_addr[i] = cache_address.set_index;
        end


        if (flush_stall) begin
            for (int i = 0; i < WAYS; i++) begin
                real_tag_array_csb0[i]   = '0;
                real_data_array_csb0[i]  = '0;
                real_valid_array_csb0[i] = '0;
                real_set_addr[i]         = flush_set_addr[SET_BITS-1:0];
            end
        end
    end

    // i chose msb bit of tag array is dirty bit
    generate for (genvar i = 0; i < WAYS; i++) begin : arrays
        mutative_data_array data_array (
            .clk0       (clk),
            .csb0       (real_data_array_csb0[i]),
            .web0       (real_web[i]),
            .wmask0     (cache_data_wmask),
            .addr0      (real_set_addr[i]),
            .din0       (cache_wdata),
            .dout0      (cache_output[i].data)
        );
        mutative_tag_array tag_array (
            .clk0       (clk),
            .csb0       (real_tag_array_csb0[i]),
            .web0       (real_web[i]),
            .addr0      (real_set_addr[i]),
            .din0       ({dirty_en, cache_address.tag}),
            .dout0      ({cache_output[i].dirty, cache_output[i].tag})
        );
        ff_array #(.S_INDEX(SET_BITS), .WIDTH(1)) valid_array (
            .clk0       (clk),
            .rst0       (rst),
            .csb0       (real_valid_array_csb0[i]),
            .web0       (real_web[i]),
            .addr0      (real_set_addr[i]),
            .din0       (1'b1),
            .dout0      (cache_output[i].valid)
        );
    end endgenerate

    mutative_comparator mut_cmp0 (
        .cache_address(cache_address),
        .cache_output(cache_output),
        .setup(setup),
        .ufp_rmask_ff(ufp_rmask_ff),
        .ufp_resp(ufp_resp),
        .hit_way(hit_way),
        .true_csb0(true_csb0),
        .hit(hit),
        .ufp_rdata(ufp_rdata)
    );

    cache_write_data_controller write_logic
    (
        .mem_write_cache(mem_write_cache),
        .write_from_cpu(write_from_cpu),
        .evict_we(evict_we),
        .dfp_rdata(dfp_rdata),
        .ufp_wdata_ff(ufp_wdata_ff),
        .ufp_wmask_ff(ufp_wmask_ff),
        .hit_way(hit_way),
        .cache_address(cache_address),
        .way_we(way_we),
        .cache_data_wmask(cache_data_wmask),
        .cache_wdata(cache_wdata),
        .dirty_en(dirty_en)
    );

    always_comb begin
        dfp_wdata = '0;
        dfp_write = '0;
        dfp_addr  = {cache_address[31:OFFSET_BITS], {OFFSET_BITS{1'b0}}};

        if (wb_en) begin
            dfp_wdata = cache_output[evict_way].data;
            dfp_write = '1;
            dfp_addr  = {cache_output[evict_way].tag, cache_address.set_index, {OFFSET_BITS{1'b0}}};
        end
        else if (flush_dfp_write) begin
            dfp_wdata = flush_dfp_wdata;
            dfp_write = '1;
            dfp_addr  = flush_dfp_addr;
        end
    end

    assign cache_wen = mem_write_cache || write_from_cpu;

    mutative_fsm #(.WAYS(8)) fsm (
        .clk(clk),
        .rst(rst),
        .cache_hit(hit),
        .cache_read_request(idle ? |ufp_rmask : |ufp_rmask_ff),
        .cache_write_request(idle ? |ufp_wmask : |ufp_wmask_ff),
        .ufp_resp(ufp_resp),
        .dfp_resp(dfp_resp),
        .dfp_read(dfp_read),
        .dfp_write(wb_en),
        .tag_array_csb0(tag_array_csb0),
        .data_array_csb0(data_array_csb0),
        .valid_array_csb0(valid_array_csb0),
        .write_from_mem(mem_write_cache),
        .write_from_cpu(write_from_cpu),
        .idle(idle),
        .dirty(cache_output[evict_way].dirty),
        .flush_stall(flush_stall)
    );

    logic plru_bit0;
    logic tie;
    mutative_plru plru (
        .clk(clk),
        .rst(rst),
        .hit_way(hit_way),
        .hit(hit),
        .cache_address(cache_address),
        .setup(setup),
        .evict_way(evict_way),
        .evict_we(evict_we),
        .left_or_right(plru_bit0),
        .tie(tie)

    );

    associativity assoc (
        .clk(clk),
        .rst(rst),
        .cache_address(cache_address),
        .cpu_request(cpu_request),
        .cache_ready(ufp_resp),
        .setup_ready(setup_ready),
        .setup(setup),
        .plru_bit0(plru_bit0),
        .tie(tie),
        .setup_update(setup_update),
        .setup_valid(setup_valid)
    );

    // Generate dirty vector signals
    always_comb begin
        valid_vector      = 'x;
        dirty_vector      = 'x;
        dirty_tag_vector  = '{default: 'x};
        dirty_data_vector = '{default: 'x};

        for (int i = 0; i < WAYS; i++) begin
            valid_vector[i] = cache_output[i].valid;
            dirty_vector[i] = cache_output[i].dirty;
            dirty_tag_vector[i] = cache_output[i].tag;
            dirty_data_vector[i] = cache_output[i].data;
        end
    end

    mutative_control setup_control (
        .clk(clk),
        .rst(rst),
        .dfp_resp(dfp_resp),
        .flush_set_addr(flush_set_addr),
        .flush_dfp_wdata(flush_dfp_wdata),
        .flush_dfp_write(flush_dfp_write),
        .flush_dfp_addr(flush_dfp_addr),
        .valid_vector(valid_vector),
        .dirty_vector(dirty_vector),
        .dirty_tag_vector(dirty_tag_vector),
        .dirty_data_vector(dirty_data_vector),
        .flush_tag_array_csb0(flush_tag_array_csb0),
        .flush_data_array_csb0(flush_data_array_csb0),
        .flush_valid_array_csb0(flush_valid_array_csb0),
        .setup_ready(setup_ready),
        .setup_valid(setup_valid),
        .setup_update(setup_update),
        .flush_stall(flush_stall),
        .setup()
    );

    assign setup = 3;

    //count accesses that each setup is in
    logic [63:0] dm_cnt, two_way_cnt, four_way_cnt, eight_way_cnt;
    logic [63:0] cycle_counter;

    logic [1:0]  prev_cache_mode;

    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            dm_cnt         <= 0;
            two_way_cnt    <= 0;
            four_way_cnt   <= 0;
            eight_way_cnt  <= 0;
            cycle_counter  <= 0;
            prev_cache_mode <= 2'b00;
        end else begin
            cycle_counter <= cycle_counter + 1;

            // Time tracking
            case (setup)
                2'b00: dm_cnt        <= dm_cnt + 1;
                2'b01: two_way_cnt   <= two_way_cnt + 1;
                2'b10: four_way_cnt  <= four_way_cnt + 1;
                2'b11: eight_way_cnt <= eight_way_cnt + 1;
            endcase

            // Change detection
            if (setup != prev_cache_mode) begin
                $display("Cache mode changed from %0d to %0d at cycle %0d", 
                          prev_cache_mode, setup, cycle_counter);
                prev_cache_mode <= setup;
            end
        end
    end

endmodule
