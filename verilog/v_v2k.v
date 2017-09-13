// DESCRIPTION: Verilog-Perl: Example Verilog for testing package
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2006-2012 by Wilson Snyder.

module v_v2k
  #(parameter WIDTH = 16) (
    input clk,
    input rst,
    input [WIDTH:0] 	 sig1,
    output reg [WIDTH:0] sig2
   );

   always @(clk) begin
      if (rst) begin
	 sig2 <= #1 0;
      end
      else begin
	 sig2 <= #1 sig1;
      end
   end

   // Multidim, bug1206
   wire [1:2] [3:4]   netmd;
   v_v2k_sub sub (.net1 (netmd[1]));

endmodule

module v_v2k_sub
  (
   input [3:4] net1
   );
endmodule
