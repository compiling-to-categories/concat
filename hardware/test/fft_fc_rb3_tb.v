/***
* fft_fc_rb3_tb.v - Test bench for automatically generated Verilog, for
*                   8-element FFT.
*
* Original author: David Banas <capn.freako@gmail.com>
* Original date:   August 22, 2017
*
* Copyright (c) 2017 David Banas; all rights reserved World wide.
***/

module fft_fc_rb3_tb;
  reg  clk;
  reg  [31:0] x0, x2, x4, x6, x8, x10, x12, x14;  // real parts
  reg  [31:0] x1, x3, x5, x7, x9, x11, x13, x15;  // imag parts
  wire [31:0] y0, y2, y4, y6, y8, y10, y12, y14;
  wire [31:0] y1, y3, y5, y7, y9, y11, y13, y15;

  fft_fc_rb3 dut (
    clk,
    x0, x1, x2,  x3,  x4,  x5,  x6,  x7,
    x8, x9, x10, x11, x12, x13, x14, x15,
    y0, y1, y2,  y3,  y4,  y5,  y6,  y7,
    y8, y9, y10, y11, y12, y13, y14, y15
    );

  initial begin
    clk = 1'b0;
    x0  = {$random} & 32'h0000FFFF;
    x2  = {$random} & 32'h0000FFFF;
    x4  = {$random} & 32'h0000FFFF;
    x6  = {$random} & 32'h0000FFFF;
    x8  = {$random} & 32'h0000FFFF;
    x10 = {$random} & 32'h0000FFFF;
    x12 = {$random} & 32'h0000FFFF;
    x14 = {$random} & 32'h0000FFFF;
    x1  = 0;
    x3  = 0;
    x5  = 0;
    x7  = 0;
    x9  = 0;
    x11 = 0;
    x13 = 0;
    x15 = 0;
    #1
    clk = 1'b1;
    #1
    clk = 1'b0;
    #1
    clk = 1'b1;
    #1
    $display("Inputs: %6d %6d %6d %6d %6d %6d %6d %6d",
             x0, x2, x4, x6, x8, x10, x12, x14);
    $display("Outputs:");
    $display("\t%6d + %6di", y0,  y1);
    $display("\t%6d + %6di", y2,  y3);
    $display("\t%6d + %6di", y4,  y5);
    $display("\t%6d + %6di", y6,  y7);
    $display("\t%6d + %6di", y8,  y9);
    $display("\t%6d + %6di", y10, y11);
    $display("\t%6d + %6di", y12, y13);
    $display("\t%6d + %6di", y14, y15);
  end

endmodule

