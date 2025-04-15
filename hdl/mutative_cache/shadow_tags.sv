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
    //cache addr = 32 bits = 23 bits for tag, 4 bits for set (16 sets), 5 bits for blk offset
    logic cpu_request, hit, wb_en;
    logic cache_wen, dirty_en;
    cache_output_t cache_output[WAYS];
    cache_address_t cache_address;
    logic [WAYS-2:0] PLRU_bits[SET_SIZE]; //N2: chooses btwn W2 and W3 N1:chooses btwn W0 and W1 N0:chooses between Ways0_1 and Ways2_3
    logic mem_write_cache;
    logic [31:0] cache_data_wmask;
    logic [255:0] cache_wdata;
    logic [WAYS-1:0] evict_we;
    logic [WAYS-1:0] way_we;
    assign cpu_request = (|ufp_rmask || |ufp_wmask);
    assign cache_address = ufp_addr;
    // i chose msb bit of tag array is dirty bit
    generate for (genvar i = 0; i < WAYS; i++) begin : arrays //TODO 
        mutative_data_array data_array (
            .clk0       (clk),
            .csb0       (1'b0), //active low  r/w  en
            .web0       (!(way_we[i]&& cache_wen)), // active low write signal TODO: look at
            .wmask0     (cache_data_wmask), 
            .addr0      (cache_address.set_index),
            .din0       (cache_wdata),
            .dout0      (cache_output[i].data)
        );
        mutative_tag_array tag_array (
            .clk0       (clk),
            .csb0       (1'b0), //active low  r/w  en
            .web0       (!(way_we[i]&& cache_wen)), // active low write signal
            .addr0      (cache_address.set_index),
            .din0       ({dirty_en, cache_address.tag}),
            .dout0      ({cache_output[i].dirty, cache_output[i].tag})
        );
        ff_array #(.WIDTH(1)) valid_array (
            .clk0       (clk),
            .rst0       (rst),
            .csb0       (1'b0), //active low  r/w  en
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
    always_comb begin: comparator_1
        hit_way = {WAY_IDX_BITS{1'b0}};
        compare_result = {WAYS{1'b0}};
        for (int unsigned i = 0; i < WAYS; i++) begin
            if(cache_output[i].valid&&(cache_output[i].tag[TAG_BITS-1:0] == cache_address.tag)) begin
                compare_result[i] = 1'b1;
                hit_way = WAY_IDX_BITS'(i); 
            end
        end
        true_data = cache_output[hit_way].data[cache_address.block_offset[4:2]*32 +: 32];
        hit = |compare_result;
        ufp_rdata = (ufp_resp && |ufp_rmask)? true_data : 'x;
    end

    always_ff @(posedge clk)begin: plru_1 //TODO: FIX MAYBE MAKE $ OF THEM
        if(rst) begin
            for(int unsigned i = 0; i < SET_SIZE; i++) begin
                PLRU_bits[i] <= {(WAYS-1){1'b0}};
            end
        end
        else if(hit)begin
            for(int i = 0; i < WAYS; i++) begin
                if(hit_way == i) 
                    PLRU_bits[cache_address.set_index] <= {PLRU_bits[cache_address.set_index][2], 2'b00};
            end


            // unique case (hit_way)
            //     2'd0: PLRU_bits[cache_address.set_index] <= {PLRU_bits[cache_address.set_index][2], 2'b00};
            //     2'd1: PLRU_bits[cache_address.set_index] <= {PLRU_bits[cache_address.set_index][2], 2'b10};
            //     2'd2: PLRU_bits[cache_address.set_index] <= {1'b0, PLRU_bits[cache_address.set_index][1], 1'b1};
            //     2'd3: PLRU_bits[cache_address.set_index] <= {1'b1, PLRU_bits[cache_address.set_index][1], 1'b1};
            // endcase
        end
    end

    logic [1:0] evict_way;
    always_comb begin : replacement_1 //TODO: MAKE 4 and FIX
        casez (~PLRU_bits[cache_address.set_index])
            3'b?00: begin
                evict_we = 4'b0001;//replace way 0
                evict_way = 2'b00;
            end
            3'b?10: begin
                evict_we = 4'b0010;//replace way 1
                evict_way = 2'b01;
            end
            3'b0?1: begin 
                evict_we = 4'b0100;//replace way 2
                evict_way = 2'b10;
            end
            3'b1?1: begin 
                evict_we = 4'b1000;//replace way 3
                evict_way = 2'b11;
            end
        endcase
    end

    //32 bits each bit represents 8 bits of 256 so 4 bits high will be 32 bti mask
    always_comb begin :cache_write_data_logic
        cache_data_wmask = 32'h00000000;
        cache_wdata = 'x;
        if(mem_write_cache) begin //memory writing cache
            way_we = evict_we;
            cache_data_wmask = 32'hFFFFFFFF;
            cache_wdata = dfp_rdata;
        end
        else if(|ufp_wmask) begin //cpu writing cache
            cache_data_wmask[4*cache_address.block_offset[4:2] +: 4] = ufp_wmask; // 00100
            cache_wdata[cache_address.block_offset[4:2]*32 +: 32] = ufp_wdata;
            for (int i=0; i<WAYS; ++i) begin
                if(hit_way == i) begin
                    way_we = 1 << i;
                end
            end
            // unique case(hit_way)
            //     2'd0: way_we = 4'b0001; 
            //     2'd1: way_we = 4'b0010;
            //     2'd2: way_we = 4'b0100;
            //     2'd3: way_we = 4'b1000;
            // endcase
        end
        else begin
            way_we = {WAYS{1'b0}};
            cache_data_wmask = 32'h00000000;
            cache_wdata = 'x;
        end
    end

    assign dfp_wdata = wb_en ? cache_output[evict_way].data : 'x;
    assign dfp_write = wb_en;
    assign dfp_addr = wb_en ? {cache_output[evict_way].tag, cache_address.set_index, {OFFSET_BITS{1'b0}}} : {cache_address[31:OFFSET_BITS], {OFFSET_BITS{1'b0}}};


    mutative_fsm control (
        .clk(clk),
        .rst(rst),
        .cpu_req(cpu_request), 
        .cache_hit(hit), 
        .cache_dirty(cache_output[evict_way].dirty), 
        .cpu_write_cache(|ufp_wmask), 
        .mem_resp(dfp_resp), 
        .cache_wen(cache_wen),
        .set_dirty(dirty_en),
        .mem_read(dfp_read),
        .mem_write_cache(mem_write_cache),
        .cache_write_mem(wb_en),
        .cache_ready(ufp_resp)
    );

endmodule