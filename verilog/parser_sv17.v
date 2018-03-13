// 1800-2017
module sv17;
   integer i;
   initial begin
      for (i=0;;) break;
      for (;i!=0;) begin end
      for (;;++i) break;
   end
endmodule
