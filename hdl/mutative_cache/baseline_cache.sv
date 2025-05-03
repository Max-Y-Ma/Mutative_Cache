module baseline_cache 
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

    always_ff @(posedge clk) begin
        if(rst) begin
            ufp_addr_ff <= '0;
            ufp_rmask_ff <= '0;
            ufp_wmask_ff <= '0;
            ufp_wdata_ff <= '0;
        end else if(idle) begin
            ufp_addr_ff <= ufp_addr;
            ufp_rmask_ff <= ufp_rmask;
            ufp_wmask_ff <= ufp_wmask;
            ufp_wdata_ff <= ufp_wdata;
        end
    end



    logic   tag_array_csb0    [WAYS-1:0];
    logic   data_array_csb0   [WAYS-1:0];
    logic   valid_array_csb0  [WAYS-1:0];
    logic   true_csb0         [WAYS-1:0];

    //cache addr = 32 bits = 23 bits for tag, 4 bits for set (16 sets), 5 bits for blk offset
    logic cpu_request, hit, wb_en;
    logic write_from_cpu;
    logic [1:0] setup; //0: DM, 1: 2-WAY, 2: 4-WAY, 3: 8-WAY
    logic cache_wen, dirty_en;
    cache_output_t cache_output[WAYS];
    cache_address_t cache_address;
    logic mem_write_cache;
    logic [31:0] cache_data_wmask;
    logic [255:0] cache_wdata;
    logic [WAYS-1:0] evict_we;
    logic [WAY_IDX_BITS-1:0] evict_way;
    logic [WAYS-1:0] way_we;
    assign cpu_request = idle ? (|ufp_rmask || |ufp_wmask) : (|ufp_rmask_ff || |ufp_wmask_ff);
    assign cache_address = idle ? ufp_addr : ufp_addr_ff;

    logic [WAYS-1:0] real_clk;
    logic [WAYS-1:0] real_csb;
    logic [WAYS-1:0] real_web;
    always_comb begin
        real_csb = '1;
        real_web = '1;
        for (int i = 0; i < WAYS; i++) begin
            real_clk[i] = clk && !true_csb0[i];
            real_csb[i] = data_array_csb0[i] || true_csb0[i];
            real_web[i] = !(way_we[i]&& cache_wen);
        end
    end

    // i chose msb bit of tag array is dirty bit
    generate for (genvar i = 0; i < WAYS; i++) begin : arrays //TODO 
        mutative_data_array data_array (
            .clk0       (real_clk[i]),
            .csb0       (real_csb[i]), //active low  r/w  en
            .web0       (real_web[i]), // active low write signal TODO: look at
            .wmask0     (cache_data_wmask), 
            .addr0      (cache_address.set_index),
            .din0       (cache_wdata),
            .dout0      (cache_output[i].data)
        );
        mutative_tag_array tag_array (
            .clk0       (real_clk[i]),
            .csb0       (real_csb[i]), //active low  r/w  en
            .web0       (real_web[i]), // active low write signal
            .addr0      (cache_address.set_index),
            .din0       ({dirty_en, cache_address.tag}),
            .dout0      ({cache_output[i].dirty, cache_output[i].tag})
        );
        ff_array #(.S_INDEX(SET_BITS), .WIDTH(1)) valid_array (
            .clk0       (real_clk[i]),
            .rst0       (rst),
            .csb0       (real_csb[i]), //active low  r/w  en
            .web0       (real_web[i]), // active low write signal
            .addr0      (cache_address.set_index),
            .din0       (1'b1), 
            .dout0      (cache_output[i].valid)
        );
    end endgenerate

    logic [WAY_IDX_BITS-1:0] hit_way;

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

    assign dfp_wdata = wb_en ? cache_output[evict_way].data : 'x;
    assign dfp_write = wb_en;
    assign dfp_addr = wb_en ? {cache_output[evict_way].tag, cache_address.set_index, {OFFSET_BITS{1'b0}}} : {cache_address[31:OFFSET_BITS], {OFFSET_BITS{1'b0}}};

    assign cache_wen = mem_write_cache || write_from_cpu;

    mutative_fsm #(.WAYS(8)) fsm (
        .clk(clk), 
        .rst(rst),
        .cache_hit(hit),
        .cache_read_request(idle ? |ufp_rmask : |ufp_rmask_ff),
        .cache_write_request(idle ? |ufp_wmask : |ufp_wmask_ff ),
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
        .dirty(cache_output[evict_way].dirty)
    );

    mutative_plru plru (
        .clk(clk), 
        .rst(rst),
        .hit_way(hit_way),
        .hit(hit),
        .cache_address(cache_address),
        .setup(setup),
        .evict_way(evict_way),
        .evict_we(evict_we)

    );



    logic full_assoc_hit;
    logic real_cache_full;
    logic full_assoc_full;
    logic real_cache_valid;

    associativity assoc (
        .clk(clk),
        .rst(rst),
        .cache_wen(cache_wen),
        .dirty_en(dirty_en),
        .ufp_addr_ff(ufp_addr_ff),
        .way_we(way_we),
        .cache_address(cache_address),
        .full_assoc_hit(full_assoc_hit),
        .real_cache_full(real_cache_full),
        .full_assoc_full(full_assoc_full),
        .valid_bit(real_cache_valid)
    );


    mutative_control setup_control (
        .clk(clk),
        .rst(rst), 
        .real_cache_valid(real_cache_valid),
        .real_cache_hit(hit),
        .full_assoc_hit(full_assoc_hit),
        .real_cache_full(real_cache_full),
        .full_assoc_full(full_assoc_full),
        .cache_ready(ufp_resp),
        .cpu_req(cpu_request),
        .setup()
    );

    assign setup = 3;

endmodule