// 1800-2009 mantis1769
module mantis1769 #(N=1);
   if (N < 1) $error("Bad N value %d", N);
endmodule
// 1800-2009 mantis1134
module mantis1134_decoder
  #(BITS = 3, localparam OUT_BITS = 1 << BITS)
   (input [BITS-1:0] A, output reg [OUT_BITS-1:0] Y);
   assign Y = 1 << A;
endmodule
// 1800-2009 mantis907
module mantis907_default_parameter
  #(REQUIRED);
endmodule
module mantis1619_default_input (input integer deflt = 10);
endmodule
module global_anal;  // Don't be anal about "global" in old code
   integer global = 1;
   global clocking z @(posedge clk);  // But still get it right
   endclocking
endmodule
module bug400;
   assert property
   ( @(posedge clk)
     disable iff (rst || $past (rst,1,,@(posedge clk)) || $isunknown(rst))
     "assert 0");
endmodule

// dobbie
package pkga;
endpackage
package pkgb;
endpackage
module impbegin
  import pkga::*;
   import pkgb::*;
   (input foobar);
endmodule


// msg2546
module def_cov_point;
   logic [7:0] data;
   logic [7:0] addr;
   covergroup c;
      ADDRESS : coverpoint addr {
         bins low[] = {[0:10]};
         bins med[] = {[11:20]};
      }
   endgroup
   // Can't handle this due to package parsing yaID__ETC
   //covergroup d;
   //   d : coverpoint data {
   //      bins low[] = {[0:10]};
   //      bins med[] = {[11:20]};
   //   }
   //endgroup
endmodule
