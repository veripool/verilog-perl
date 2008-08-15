// DESCRIPTION: Verilog-Perl: Example Verilog for testing package
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2003 by Wilson Snyder.

module pinorder4();
   wire b_i;
   wire d_o;
   wire [7:0] a_i;
   wire [31:0] IPCD_const = 32'h1;

   assign      a_i = 0;
   assign      b_i = 0;

   foo foo1( .y(b_i), .x(a_i), .abcconst(3'h0), .noconnect(),
	     .def(IPCD_const));
   foo foo3( b_i, a_i, 3'h0, , IPCD_const);
   foo2 foo2( b_i, a_i[0], d_o);

endmodule

module foo2(/*AUTOARG*/
   // Outputs
   x,
   // Inputs
   z, y
   );
   input z;
   input y;
   output x;
   reg x;
   always @(z or y) x = z & y;
endmodule

module foo (/*AUTOARG*/
   // Inputs
   y, x, abcconst, noconnect, def
   );
   input y;
   input x;
   input [2:0] abcconst;
   input signed [3:0] noconnect;
   input [31:0] def;
endmodule
