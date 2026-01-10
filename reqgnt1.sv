module reqgnt(
    input logic clk,
    input logic rst,
    input logic req,
    input logic gnt
);

// --- AUXILIARY CODE ---

reg signed [4:0] cnt;

always @(posedge clk) begin
    if(rst) cnt <= 5'b00000;
    else begin
        if (req && ~gnt) cnt <= cnt + 1;
        if (~req && gnt) cnt <= cnt -1;
    end
end

reg [2:0] sym_idx;
stable_sym_idx: assume property (@(posedge clk) $stable(sym_idx));
  
reg [7:0] aux_fifo;
reg [2:0] req_ptr, gnt_ptr;
logic full, empty;

assign full = (cnt == 8);
assign empty = (cnt == 0);

always_ff @(posedge clk) begin
    if (rst) begin
        aux_fifo <= 8'b0;
        req_ptr <= 3'b0;
        gnt_ptr <= 3'b0;
    end
    else begin
        if (req && !full) begin
            aux_fifo[req_ptr] <= 1;
            req_ptr <= (req_ptr == 7) ? 0 : req_ptr + 1;
        end
        if (gnt && !empty) begin
            aux_fifo[gnt_ptr] <= 0;
            gnt_ptr <= (gnt_ptr == 7) ? 0 : gnt_ptr + 1;
        end
    end
end

// --- PROPERTY ---

property P;
    @(posedge clk) disable iff (rst)
    
    (cnt >= 0 && cnt <= 8)
    
    and (gnt |-> cnt > 0)
    
    and ((~aux_fifo[sym_idx] ##1 aux_fifo[sym_idx]) |=> (aux_fifo[sym_idx] ##[2:8] ~aux_fifo[sym_idx]))
    
    and (gnt |-> aux_fifo[gnt_ptr] ##1 !aux_fifo[$past(gnt_ptr)]); 
    
endproperty

A: assert property (P);

endmodule
