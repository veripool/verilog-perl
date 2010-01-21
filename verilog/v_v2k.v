// DESCRIPTION: Verilog-Perl: Example Verilog for testing package
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2006-2010 by Wilson Snyder.

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
endmodule
