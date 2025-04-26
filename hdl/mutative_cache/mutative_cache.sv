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

    //cache addr = 32 bits = 23 bits for tag, 4 bits for set (16 sets), 5 bits for blk offset
    logic cpu_request, hit, wb_en;
    logic write_from_cpu;
    logic [1:0] setup; //0: DM, 1: 2-WAY, 2: 4-WAY, 3: 8-WAY
    logic cache_wen, dirty_en;
    cache_output_t cache_output[WAYS];
    cache_address_t cache_address;
    logic [WAYS-2:0] PLRU_bits[SET_SIZE]; //N2: chooses btwn W2 and W3 N1:chooses btwn W0 and W1 N0:chooses between Ways0_1 and Ways2_3
    logic mem_write_cache;
    logic [31:0] cache_data_wmask;
    logic [255:0] cache_wdata;
    logic [WAYS-1:0] evict_we;
    logic [WAY_IDX_BITS-1:0] evict_way;
    logic [WAYS-1:0] way_we;
    assign cpu_request = idle ? (|ufp_rmask || |ufp_wmask) : (|ufp_rmask_ff || |ufp_wmask_ff);
    assign cache_address = idle ? ufp_addr : ufp_addr_ff;
    // i chose msb bit of tag array is dirty bit
    generate for (genvar i = 0; i < WAYS; i++) begin : arrays //TODO 
        mutative_data_array data_array (
            .clk0       (clk),
            .csb0       (data_array_csb0[i]), //active low  r/w  en
            .web0       (!(way_we[i]&& cache_wen)), // active low write signal TODO: look at
            .wmask0     (cache_data_wmask), 
            .addr0      (cache_address.set_index),
            .din0       (cache_wdata),
            .dout0      (cache_output[i].data)
        );
        mutative_tag_array tag_array (
            .clk0       (clk),
            .csb0       (tag_array_csb0[i]), //active low  r/w  en
            .web0       (!(way_we[i]&& cache_wen)), // active low write signal
            .addr0      (cache_address.set_index),
            .din0       ({dirty_en, cache_address.tag}),
            .dout0      ({cache_output[i].dirty, cache_output[i].tag})
        );
        ff_array #(.S_INDEX(SET_BITS), .WIDTH(1)) valid_array (
            .clk0       (clk),
            .rst0       (rst),
            .csb0       (valid_array_csb0[i]), //active low  r/w  en
            .web0       (!(way_we[i]&& cache_wen)), // active low write signal
            .addr0      (cache_address.set_index),
            .din0       (1'b1), 
            .dout0      (cache_output[i].valid)
        );
    end endgenerate

    logic [WAYS-1:0] compare_result;
    logic [31:0] true_data;
    logic true_valid;
    logic [WAY_IDX_BITS-1:0] hit_way;
    logic [2:0] dm_way_index;
    logic [1:0] two_way_index;
    logic four_way_index;
    always_comb begin: comparator_1
        hit_way = {WAY_IDX_BITS{1'b0}};
        compare_result = {WAYS{1'b0}};
        dm_way_index = cache_address.tag[2:0];
        two_way_index = cache_address.tag[1:0]; //0-3
        four_way_index = cache_address.tag[0];
        if(setup == 0) begin //DM 
            if(cache_output[dm_way_index].valid&&(cache_output[dm_way_index].tag[TAG_BITS-4:0] == cache_address.tag[TAG_BITS-4:0])) begin
                compare_result[dm_way_index] = 1'b1;
                hit_way = WAY_IDX_BITS'(dm_way_index); 
            end
        end else if(setup == 1) begin //2-way
            for (int unsigned i = 0; i < (WAYS/4); i++) begin
                if(cache_output[i+ (WAYS/4)*two_way_index].valid&&(cache_output[i+ (WAYS/4)*two_way_index].tag[TAG_BITS-3:0] == cache_address.tag[TAG_BITS-3:0])) begin
                    compare_result[i+ (WAYS/4)*two_way_index] = 1'b1;
                    hit_way = WAY_IDX_BITS'(i+ (WAYS/4)*two_way_index); 
                end
            end
        end else if(setup == 2) begin //4-way
            for (int unsigned i = 0; i < (WAYS/2); i++) begin
                if(cache_output[i+ (WAYS/2)*four_way_index].valid&&(cache_output[i+ (WAYS/2)*four_way_index].tag[TAG_BITS-2:0] == cache_address.tag[TAG_BITS-2:0])) begin
                    compare_result[i+ (WAYS/2)*four_way_index] = 1'b1;
                    hit_way = WAY_IDX_BITS'(i+ (WAYS/2)*four_way_index); 
                end
            end
        end else begin //8-way
            for (int unsigned i = 0; i < WAYS; i++) begin
                if(cache_output[i].valid&&(cache_output[i].tag[TAG_BITS-1:0] == cache_address.tag)) begin
                    compare_result[i] = 1'b1;
                    hit_way = WAY_IDX_BITS'(i); 
                end
            end
        end
        true_data = cache_output[hit_way].data[cache_address.block_offset[4:2]*32 +: 32];
        hit = |compare_result;
        ufp_rdata = (ufp_resp && |ufp_rmask_ff)? true_data : 'x;
    end

    //32 bits each bit represents 8 bits of 256 so 4 bits high will be 32 bti mask
    always_comb begin :cache_write_data_logic
        cache_data_wmask = 32'h00000000;
        cache_wdata = 'x;
        dirty_en = 1'b0;
        if(mem_write_cache) begin //memory writing cache
            way_we = evict_we;
            cache_data_wmask = 32'hFFFFFFFF;
            cache_wdata = dfp_rdata;
            dirty_en = 1'b0;
        end
        else if(write_from_cpu) begin //cpu writing cache
            cache_data_wmask[4*cache_address.block_offset[4:2] +: 4] = ufp_wmask_ff; // 00100
            cache_wdata[cache_address.block_offset[4:2]*32 +: 32] = ufp_wdata_ff;
            way_we = 1 << hit_way;
            dirty_en = 1'b1;
        end
        else begin
            way_we = {WAYS{1'b0}};
            cache_data_wmask = 32'h00000000;
            cache_wdata = 'x;
            dirty_en = 1'b0;
        end
    end

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



    logic [FULL_TAG_BITS-1:0]       full_assoc_tag;
    full_assoc_t                    full_assoc_cache[SET_SIZE*WAYS];
    logic                           full_assoc_hit;
    logic [FULL_ASSOC_BITS-1:0]     full_assoc_hit_idx;

    assign full_assoc_tag = ufp_addr_ff >> OFFSET_BITS;

    always_ff @(posedge clk) begin
        if(rst) begin
            for(int i = 0; i < (SET_SIZE*WAYS); i++)
                full_assoc_cache[i] <= '0;
        end else if(cache_wen) begin
            full_assoc_cache[full_assoc_hit_idx].valid <= 1'b1;
            full_assoc_cache[full_assoc_hit_idx].dirty <= dirty_en;
            full_assoc_cache[full_assoc_hit_idx].tag <= full_assoc_tag;
        end
    end

    always_comb begin //comparator 
        full_assoc_hit_idx = '0;
        full_assoc_hit = 1'b0;
        for (int i=0; i < (SET_SIZE*WAYS); ++i) begin
            if(full_assoc_tag == full_assoc_cache[i].tag && full_assoc_cache[i].valid) begin
                full_assoc_hit = 1'b1;
                full_assoc_hit_idx = i;
                break;
            end
        end
    end

    
    logic virt_valid_array[SET_SIZE][WAYS];
    always_ff @(posedge clk) begin
        if(rst) begin
            for(int i = 0; i < SET_SIZE; i++) begin
                for(int j = 0; j < WAYS; j++) begin
                    virt_valid_array[i][j] <= '0;
                end
            end
        end else if(cache_wen) begin
            for(int i = 0; i < WAYS; i++) begin
                if(way_we[i]) begin
                    virt_valid_array[cache_address.set_index][i] <= 1'b1;
                end
            end

        end
    end

    logic real_cache_full;
    logic full_assoc_full;
    always_comb begin
        real_cache_full = 1'b1;
        full_assoc_full = 1'b1;
        for(int i = 0; i < SET_SIZE; i++) begin
            for(int j = 0; j < WAYS; j++) begin
                if(virt_valid_array[i][j] == 0) begin
                    real_cache_full = 1'b0;
                end
            end
        end
        for (int k=0; k<(SET_SIZE*WAYS); ++k) begin
            if(full_assoc_cache[k].valid == 0) begin
                full_assoc_full = 1'b0;
            end
        end
    end


    mutative_control setup_control (
        .clk(clk),
        .rst(rst), 
        .real_cache_valid(full_assoc_cache[full_assoc_hit_idx].valid),
        .real_cache_hit(hit),
        .full_assoc_hit(full_assoc_hit),
        .real_cache_full(real_cache_full),
        .full_assoc_full(full_assoc_full),
        .cache_ready(ufp_resp),
        .cpu_req(cpu_request),
        .setup(setup)
        );

endmodule