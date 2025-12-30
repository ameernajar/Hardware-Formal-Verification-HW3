module reqgnt(
    input logic clk,
    input logic rst,
    input logic req,
    input logic gnt
);

// Instructions:
// 1. Implement "property P;" below.
// 2. Use auxiliary code.
// 3. Do not change the name of the property (keep it "P").
// 4. Do not change the label of the assert (keep it "A").

// IMPLEMENT THE AUXILIARY CODE HERE

// since every req should be served withen 8 cycles, we can have 8 unserved reqs at most
// thus, for the counter, we need 4 bits +1 for sign bit .
// by 4 bits we can represent > 8, we make sure that doesnt happen. 
  
reg signed [4:0] cnt;

always @(posedge clk) begin
	if(rst) cnt <= 5'b00000;
	else begin
		if (req && ~gnt) cnt <= cnt + 1;
		if (~req && gnt) cnt <= cnt -1;
	end
end


// symbolic variable presenting an index in the fifo.
reg [2:0] sym_idx;
stable_sym_idx: assume property (@(posedge clk) $stable(sym_idx));
  
  
// auxiliary fifo to help us track reqs and gnts by order.
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
		if (req && gnt && req_ptr == gnt_ptr) begin
			/* do nothing */
		end else begin
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
  



property P;
    @(posedge clk) (cnt >= 0 && cnt <= 8) && 
	(req && (req_ptr == sym_idx)|-> aux_fifo[sym_idx] ##1 aux_fifo[sym_idx] ##[1:7] (gnt && gnt_ptr == sym_idx)); // IMPLEMENT THE PROPERTY HERE
endproperty

A: assert property (P);

endmodule
