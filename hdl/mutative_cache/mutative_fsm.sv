module mutative_fsm (
    input   logic           clk,
    input   logic           rst,

    input   logic           cpu_req, //read/write request
    input   logic           cache_hit, // comparator output
    input   logic           cache_dirty, // dirty bit (msb bit of tag)
    input   logic           cpu_write_cache, //write signal (0: read, 1: write cpu request)
    input   logic           mem_resp, //main memory response

    output  logic           cache_wen, //write to cache
    output  logic           set_dirty, //set dirty bit
    output  logic           mem_read,
    output  logic           mem_write_cache,
    output  logic           cache_write_mem,
    output  logic           cache_ready
);
    //if never written to from mem (valid == 0) or not a match (hit == 0) go to allocate in both states? 
    //when memory is ready do you write to cache in allocate or in compare tag state and how do u set dirty
    enum logic [2:0] {
        s_idle, s_compare_tag, 
        s_allocate, s_alllocate_idle, s_write_back
    } cache_state, cache_state_next;
    //TODO: think about routing to idle from allocate

    always_ff @( posedge clk ) begin
        if (rst) begin
            cache_state <= s_idle;
        end else begin
            cache_state <= cache_state_next;
        end
    end

    always_comb begin
        cache_state_next = cache_state;
        cache_wen = 1'b0;
        set_dirty = 1'b0;
        mem_read = 1'b0;
        mem_write_cache = 1'b0;
        cache_write_mem = 1'b0;
        cache_ready = 1'b0;

        unique case (cache_state)
            s_idle: begin 
                if(cpu_req) begin
                    cache_state_next = s_compare_tag;
                end
            end
            s_compare_tag: begin
                if(cache_hit) begin 
                    cache_state_next = s_idle;
                    set_dirty = cpu_write_cache;
                    cache_ready = 1'b1;
                    cache_wen = cpu_write_cache;
                end
                else if(cache_dirty) begin
                    cache_state_next = s_write_back;
                end
                else begin
                    cache_state_next = s_allocate;
                end
            end
            s_allocate: begin
                mem_read = 1'b1;
                if(mem_resp) begin
                    cache_wen = 1'b1;
                    cache_state_next = s_alllocate_idle;
                    mem_write_cache = 1'b1;
                end 
            end
            s_alllocate_idle: begin
                cache_state_next = s_compare_tag;
            end
            s_write_back: begin
                cache_write_mem = 1'b1;
                if(mem_resp) begin
                    cache_state_next = s_allocate;
                end
            end
            default: begin
                cache_state_next = cache_state;
                cache_wen = 1'b0;
                set_dirty = 1'b0;
                mem_read = 1'b0;
                mem_write_cache = 1'b0;
                cache_write_mem = 1'b0;
                cache_ready = 1'b0;
            end
        endcase
    end
endmodule