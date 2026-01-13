module reqgnt(
    input logic clk,
    input logic rst,
    input logic req,
    input logic gnt
);

// --- IMPLEMENT THE AUXILIARY CODE HERE ---

// 1. Counter for number of pending requests
reg signed [4:0] cnt;

always @(posedge clk) begin
    if(rst) cnt <= 5'b00000;
    else begin
        // If both happen simultaneously, counter remains the same
        if (req && gnt) 
            cnt <= cnt;
        else if (req) 
            cnt <= cnt + 1;
        else if (gnt) 
            cnt <= cnt - 1;
    end
end

// 2. Symbolic variable for tracking specific request
reg [2:0] sym_idx;
stable_sym_idx: assume property (@(posedge clk) $stable(sym_idx));
  
// 3. Auxiliary FIFO
reg [7:0] aux_fifo;
reg [2:0] req_ptr, gnt_ptr;
wire full, empty;

assign full = (cnt == 8);
assign empty = (cnt == 0);

always_ff @(posedge clk) begin
    if (rst) begin
        aux_fifo <= 8'b0;
        req_ptr <= 3'b0;
        gnt_ptr <= 3'b0;
    end
    else begin
        // Handle Request
        if (req && !full) begin
            aux_fifo[req_ptr] <= 1'b1;
            req_ptr <= req_ptr + 1;
        end
        // Handle Grant
        if (gnt && !empty) begin
            aux_fifo[gnt_ptr] <= 1'b0;
            gnt_ptr <= gnt_ptr + 1;
        end
    end
end

// --- PROPERTY IMPLEMENTATION ---

property P;
    // CRITICAL: Disable check during reset
    @(posedge clk)  
    
    // 1. Bounds check (0 to 8 pending requests)
    (cnt >= 0 && cnt <= 8) 
    
    // 2. No grant allowed if queue is empty
    and (cnt == 0 |-> !gnt ) 
    
    // 3. Timing check: 
    // When a specific request enters ($rose), it must be cleared ($fell) 
    // within 2 to 8 cycles.
    and ($rose(aux_fifo[sym_idx]) |-> ##[2:8] $fell(aux_fifo[sym_idx])); 
    
endproperty

A: assert property (P);

endmodule
