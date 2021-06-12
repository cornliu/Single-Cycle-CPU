// https://u.cyberlink.com/live/937601414790645567
// Your code

module CHIP(clk,
            rst_n,
            // For mem_D
            mem_wen_D,
            mem_addr_D,
            mem_wdata_D,
            mem_rdata_D,
            // For mem_I
            mem_addr_I,
            mem_rdata_I);

    input         clk, rst_n ;
    // For mem_D
    output reg    mem_wen_D  ; // 0: Read data from data/stack memory, 1: Write data to data/stack memory
    output reg [31:0] mem_addr_D ; // Address of data/stack memory
    output reg [31:0] mem_wdata_D; // Data written to data/stack memory
    input  [31:0] mem_rdata_D; // Data read from data/stack memory
    // For mem_I
    output reg [31:0] mem_addr_I ; // Address of instruction (text) memory
    input  [31:0] mem_rdata_I; // Instruction read from instruction (text) memory
    
    
    //---------------------------------------//
    // Do not modify this part!!!            //
    // Exception: You may change wire to reg //
    reg    [31:0] PC          ;              //
    reg    [31:0] PC_nxt      ;              //
    reg           regWrite    ;              //
    reg    [ 4:0] rs1, rs2, rd;              //
    wire   [31:0] rs1_data    ;              //
    wire   [31:0] rs2_data    ;              //
    wire   [31:0] rd_data     ;              //
    //---------------------------------------//

    // Todo: other wire/reg
    reg [31:0] Instruction_all ; // instruction code
    reg [31:0] load_data ; // data read from data/stack memory
    reg [31:0] save_data ; // write data to data memory
    reg [6:0] opcode ; // Instruction_all[6:0]
    reg [31:0] Imm; // Immediate = Instruction_all[31:0]
    wire [31:0] Imm_Gen; // expand Immediate
    wire [31:0] ALU_result ; // result from ALU
    wire [31:0] ALU_In2 ; // ALU input_2
    wire [3:0] control ; // control signal
    wire [31:0] mux_out_1; // mux after data memory
    wire [31:0] mux_out_2; 

    // control signal for different blocks
    wire Zero;
    reg Jalr, Jal, Branch, MemRead, MemtoReg, MemWrite, ALUSrc, Auipc, JalJalr;
    reg [4:2] ALUOp ;

    // PC signal
    reg [31:0] PCAdd4; // PC add 4
    reg [31:0] PC_offset; // PC for branch
    reg [31:0] PC_jal; // PC for jump
    reg [31:0] PC_jalr; // PC for jump and link
    wire [63:0] muldiv_result; // result from muldiv
    wire muldiv_valid; // start muldiv
    wire muldiv_ready; // result is ready
    wire muldiv_mode; // for mul or div

    //---------------------------------------//
    // Do not modify this part!!!            //
    reg_file reg0(                           //
        .clk(clk),                           //
        .rst_n(rst_n),                       //
        .wen(regWrite),                      //
        .a1(rs1),                            //
        .a2(rs2),                            //
        .aw(rd),                             //
        .d(rd_data),                         //
        .q1(rs1_data),                       //
        .q2(rs2_data));                      //
    //---------------------------------------//
    
    // Todo: any combinational/sequential circuit
    ALU ALU_instance(.result(ALU_result), .zero(Zero), .In1(rs1_data), .In2(ALU_In2), .control(control), .mult_valid(muldiv_valid), .mult_ready(muldiv_ready), .mul_answer(muldiv_result));
    ALU_control ALU_control_instance(.ALUOp(ALUOp), .bit_30(Imm[30]), .bit_25(Imm[25]), .function3(Imm[14:12]), .control(control));
    mux_32 mux_before_ALU_instance(.Out(ALU_In2), .In0(rs2_data), .In1(Imm_Gen), .control(ALUSrc));
    mux_32 mux_after_data_memory(.Out(mux_out_1), .In0(ALU_result), .In1(load_data), .control(MemtoReg));
    mux_32 mux_after_mux_for_jal(.Out(mux_out_2), .In0(mux_out_1), .In1(PCAdd4), .control(JalJalr));
    mux_32 mux_after_mux_for_auipc(.Out(rd_data), .In0(mux_out_2), .In1(PC_offset), .control(Auipc));
    Imm_Gen Imm_Gen_block(.Imm_Gen(Imm_Gen), .Imm(Imm));
    mulDiv mymul(.clk(clk), .rst_n(rst_n), .valid(mult_valid), .ready(mult_ready), .mode(mult_mode), .in_A(rs1_data), .in_B(ALU_In2), .out(muldiv_result));

    // sequential circuit
    // conbinational circuit
    // set bits into register
    assign mult_mode = 1'b0 ;

    always@(*)
    begin
        // input from memory
        //instruction[31:0] = {mem_rdata_I[7:0], mem_rdata_I[15:8], mem_rdata_I[23:16], mem_rdata_I[31:24]} ;
        //load_data[31:0] = {mem_rdata_D[7:0], mem_rdata_D[15:8], mem_rdata_D[23:16], mem_rdata_D[31:24]} ;
        instruction = mem_rdata_I;
        load_data = mem_rdata_D ;

        opcode = instruction[6:0];
        rs1 = instruction[19:15];
        rs2 = instruction[24:20];
        rd = instruction[11:7];
        Imm = instruction[31:0];

        // set control signal
        // jalr = 0, jal = 0, branch = 0, memread = 0, memtoreg = 0, ALUOp = 3'b000, memwrite = 0 , regWrite = 0, ALUSrc = 0, jal_or_jalr = 0, auipc_or_not = 0
        
        case(opcode)
        7'b0110011: //and, sub, add, or, slt, mul
        begin
            JalJalr = 0 ;
            Jalr = 0 ;
            Jal = 0 ;
            Branch = 0 ;
            MemRead = 0 ;
            MemtoReg = 0 ;
            MemWrite = 0 ;
            if (muldiv_valid == 1 && muldiv_ready == 0) 
            begin
                regWrite = 0;
            end
            else 
            begin
                regWrite = 1;
            end
            ALUOp = 3'b111; 
            ALUSrc = 0 ;
        end
        7'b0010011: // addi, slti
        begin
            jal_or_jalr = 0 ;
            jalr = 0 ;
            jal = 0 ;
            branch = 0 ;
            memread = 0 ;
            memtoreg = 0 ;
            memwrite = 0 ;
            regWrite = 1 ;
            ALUOp = 3'b110; 
            ALUSrc = 1 ;
        end
        7'b0000011: //lw
        begin
            jal_or_jalr = 0 ;
            jalr = 0 ;
            jal = 0;
            branch = 0 ;
            memread = 1 ;
            memtoreg = 1 ;
            ALUOp = 3'b100;
            memwrite = 0 ;
            ALUSrc = 1 ;
            regWrite = 1 ;
        end
        7'b0100011: //sw
        begin
            jal_or_jalr = 0 ;
            jalr = 0 ;
            jal = 0 ;
            branch = 0 ;
            memread = 0 ;
            memtoreg = 0 ;
            ALUOp = 3'b101 ;
            memwrite = 1 ;
            ALUSrc = 1 ;
            regWrite = 0 ;
        end
        7'b1100011: //beq
        begin
            jal_or_jalr = 0 ;
            jalr = 0 ;
            jal = 0 ;
            branch = 1 ;
            memread = 0 ;
            memtoreg = 0 ;
            ALUOp = 3'b011;
            memwrite = 0 ;
            ALUSrc = 0 ;
            regWrite = 0 ;
        end
        7'b1101111: //jal
        begin
            jal_or_jalr = 1 ;
            jalr = 0 ;
            jal = 1 ;
            branch = 0 ;
            memread = 0 ;
            memtoreg = 0 ;
            ALUOp = 3'b001;
            memwrite = 0 ;
            ALUSrc = 1 ;
            regWrite = 1 ;
        end
        7'b1100111: //jalr  
        begin
            jal_or_jalr = 1 ;
            jalr = 1;
            jal = 0 ;
            branch = 0 ;
            memread = 0 ;
            memtoreg = 0 ;
            ALUOp = 3'b010 ;
            memwrite = 0 ;
            ALUSrc = 1 ;
            regWrite = 1 ;
        end
        7'b0010111: //auipc  
        begin
            jal_or_jalr = 0 ;
            jalr = 0;
            jal = 0 ;
            branch = 0 ;
            memread = 0 ;
            memtoreg = 0 ;
            ALUOp = 3'b000 ;
            memwrite = 0 ;
            ALUSrc = 1 ;
            regWrite = 1 ;
            auipc_or_not = 1 ;
        end
        default   
        begin
            jal_or_jalr = 0 ;
            jalr = 0 ;
            jal = 0 ;
            branch = 0 ;
            memread = 0 ;
            memtoreg = 0 ;
            ALUOp = 3'b000 ;
            memwrite = 0 ;
            regWrite = 0 ;
            ALUSrc = 0 ;
        end
        endcase

        // set PC signal 
        PC_4 <= PC + 4  ;
        PC_offset = PC + Imm_Gen ;
        PC_jal = ((branch & zero) ^ jal) ? PC_offset : PC_4 ;
        PC_jalr = Imm_Gen + rs1_data ;

        if (rst_n==0)
        	PC_nxt = 0 ;
        else if (mult_valid == 1 && mult_ready == 0) 
        begin
            PC_nxt = PC ;
        end
        else
        	PC_nxt = jalr ? PC_jalr : PC_jal ;

        // 
        save_data = memwrite ? rs2_data : 0 ;
        //mem_wdata_D[31:0] = {save_data[7:0], save_data[15:8], save_data[23:16], save_data[31:24]} ;
        mem_wdata_D = save_data ;

        // mem_wen_D == 0 read , mem_wen_D == 1 write
        mem_wen_D = memwrite ;
        mem_addr_D = ALU_result ;
        /*
        if (rst_n==0)
        	mem_addr_I = 0 ;
        else
        	mem_addr_I = {25'b0,PC,2'b0} ;
        */
        mem_addr_I = PC ;

    end

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            PC <= 32'h00010000; // Do not modify this value!!!
            
        end
        else begin
            PC <= PC_nxt;
            
        end
    end
endmodule

module reg_file(clk, rst_n, wen, a1, a2, aw, d, q1, q2);
   
    parameter BITS = 32;
    parameter word_depth = 32;
    parameter addr_width = 5; // 2^addr_width >= word_depth
    
    input clk, rst_n, wen; // wen: 0:read | 1:write
    input [BITS-1:0] d;
    input [addr_width-1:0] a1, a2, aw;

    output [BITS-1:0] q1, q2;

    reg [BITS-1:0] mem [0:word_depth-1];
    reg [BITS-1:0] mem_nxt [0:word_depth-1];

    integer i;

    assign q1 = mem[a1];
    assign q2 = mem[a2];

    always @(*) begin
        for (i=0; i<word_depth; i=i+1)
            mem_nxt[i] = (wen && (aw == i)) ? d : mem[i];
    end

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            mem[0] <= 0;
            for (i=1; i<word_depth; i=i+1) begin
                case(i)
                    32'd2: mem[i] <= 32'hbffffff0;
                    32'd3: mem[i] <= 32'h10008000;
                    default: mem[i] <= 32'h0;
                endcase
            end
        end
        else begin
            mem[0] <= 0;
            for (i=1; i<word_depth; i=i+1)
                mem[i] <= mem_nxt[i];
        end       
    end
endmodule

module mulDiv(clk, rst_n, valid, ready, mode, in_A, in_B, out);
    // Todo: your HW2
    // Definition of ports
    input         clk, rst_n;
    input         valid, mode; // mode: 0: mulu, 1: divu
    output        ready;
    input  [31:0] in_A, in_B;
    output [63:0] out;

    // Definition of states
    parameter IDLE = 2'b00;
    parameter MUL  = 2'b01;
    parameter DIV  = 2'b10;
    parameter OUT  = 2'b11;

    // Todo: Wire and reg if needed
    reg  [ 1:0] state, state_nxt;
    reg  [ 4:0] counter, counter_nxt;
    reg  [63:0] shreg, shreg_nxt;
    reg  [31:0] alu_in, alu_in_nxt;
    reg  [32:0] alu_out;

    // Todo: Instatiate any primitives if needed

    // Todo 5: Wire assignments
    assign ready = &state; 
    assign out = shreg_nxt;

    // Combinational always block
    // Todo 1: Next-state logic of state machine
    always @(*) begin // implement always block if signal changes
        case(state)
            IDLE: begin
                if (~valid) state_nxt = state; // valid == 0，keep IDLE
                else begin
                    if (mode) state_nxt = DIV; // mode == 1，DIV
                    else state_nxt = MUL; // mode == 0，MUL
                end
            end
            MUL : state_nxt = (counter != 31)?state: OUT; // if counter == 31，OUT
            DIV : state_nxt = (counter != 31)?state: OUT; // if counter == 31，OUT
            OUT : state_nxt = IDLE;
        endcase
    end
    
    // Todo 2: Counter
    always @(*) begin // implement always block if signal changes
        case(state)
            IDLE: counter_nxt = 0;
            MUL : counter_nxt = (counter != 31)?counter + 1: 0; 
            DIV : counter_nxt = (counter != 31)?counter + 1: 0; 
            OUT : counter_nxt = 0;
        endcase  
    end   
    
    // ALU input
    always @(*) begin
        case(state)
            IDLE: begin
                if (valid) alu_in_nxt = in_B;
                else       alu_in_nxt = 0;
            end
            OUT : alu_in_nxt = 0;
            default: alu_in_nxt = alu_in;
        endcase
    end

    // Todo 3: ALU output
    always @(*) begin
        case(state)
            IDLE: alu_out = {1'b0, shreg[63:32]};
            MUL : begin
                if (~shreg[0]) alu_out = {1'b0, shreg[63:32]}; // fill msb with 1'b0
                else alu_out = {1'b0, alu_in} + {1'b0, shreg[63:32]}; // fill msb with 1'b0              
            end
            DIV : begin
                alu_out = shreg[63:31] - {1'b0, alu_in};
            end
            OUT : alu_out = {1'b0, shreg[63:32]};
        endcase
    end   
    
    // Todo 4: Shift register
    always @(*) begin
        case(state)
            IDLE: begin
                if (valid) shreg_nxt = {32'b0, in_A};
                else shreg_nxt = 64'b0;
            end
            MUL : begin
                shreg_nxt = {alu_out, shreg[31:1]}; // shift right
            end
            DIV : begin
                if (alu_out[32]) shreg_nxt = {shreg[62:0], 1'b0}; // shift left
                else shreg_nxt = {alu_out[31:0], shreg[30:0], 1'b1}; // shift left
            end
            OUT : shreg_nxt = shreg;
        endcase
    end   

    // Todo: Sequential always block
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin // rst_n == 0: reset，state = IDLE
            state <= IDLE;
            alu_in  <= 0;
            shreg   <= 0;
            counter <= 0;
        end
        else begin
            state <= state_nxt;
            alu_in  <= alu_in_nxt;
            shreg   <= shreg_nxt;
            counter <= counter_nxt;
        end
    end

endmodule

module ALU(result, zero, In1, In2, control, mult_valid, mult_ready, mul_answer);
output reg [31:0] result;
output reg zero; //equal or not for branch
input [31:0] In1, In2;
input [3:0] control ; // ALUControl
output reg mult_valid;
input  mult_ready;
input [63:0] mul_answer ;
always@(*)
begin
    // default
    result = 0 ;
    zero = 0 ;
    mult_valid = 0 ;
    case(control)
        4'b0000: // add, addi 
        begin
            result = $signed(In1) + $signed(In2) ; 
            zero = 0 ;
        end
        4'b0001:
        begin
            result = In1 >> In2 ;
            zero = 0 ;
        end
        4'b0010: //slt, slti 
        begin
            if ( $signed(In1) < $signed(In2) )
                result = 1;
            else 
                result = 0;
            zero = 0 ;
        end
        4'b0100: // mul 
        begin
            mult_valid = 1'b1 ;
            if (mult_ready == 1)
                result = mul_answer[31:0] ;
            else
                result = 0 ;
            zero = 0 ;
        end
        4'b1000: // sub 
        begin
            result = $signed(In1) - $signed(In2) ;
            if (In1 == In2)
                zero = 1 ;
            else 
                zero = 0 ;
        end
        default 
        begin
            zero = 0 ;
            result = 0 ;
        end
    endcase
end
endmodule

module ALU(result, zero, In1, In2, control, mult_valid, mult_ready, mul_answer);
output reg [31:0] result;
output reg zero; //equal or not for branch
input [31:0] In1, In2;
input [3:0] control ; // control 要在哪看不確定
output reg mult_valid;
input  mult_ready;
input [63:0] mul_answer ;
reg carry; 
always@(*)
begin
    // default
    result = 0 ;
    carry = 0 ;
    zero = 0 ;
    mult_valid = 0 ;
    case(control)
        4'b0001:
        begin
            result = In1 >> In2 ;
            zero = 0 ;
        end
        4'b0000: // add, addi 
        begin
            {carry,result} = $signed(In1) + $signed(In2) ; 
            zero = 0 ;
        end
        4'b1000: // sub 
        begin
            {carry,result} = $signed(In1) - $signed(In2) ;
            if (In1 == In2)
                zero = 1 ;
            else 
                zero = 0 ;
        end
        4'b0010: //slt, slti 
        begin
            if ( $signed(In1) < $signed(In2) )
                result = 1;
            else 
                result = 0;
            zero = 0 ;
        end
        4'b0100: // mul 
        begin
            mult_valid = 1'b1 ;
            if (mult_ready == 1)
                result = mul_answer[31:0] ;
            else
                result = 0 ;
            zero = 0 ;
        end
        default 
        begin
            zero = 0 ;
            result = 0 ;
            carry = 0 ;
        end
    endcase
end
endmodule

// ALU control 
module ALU_control(ALUOp, bit_30, bit_25, function3, control);
input bit_30;
input bit_25; 
input [2:0] ALUOp ; // 為什麼是三碼不太確定
input [2:0] function3;
// 看起來這段是類似某個 kmap?
output [3:0] control ; // 輸出 ALU output
assign control[0] = ALUOp[2] & ALUOp[1] & (!ALUOp[0]) & function3[2];
assign control[1] = function3[1] & ALUOp[1];
assign control[2] = bit_25 & ALUOp[0] & ALUOp[1] & ALUOp[2] ;
assign control[3] = (!ALUOp[2]) | (bit_30 & ALUOp[2] & ALUOp[1] & ALUOp[0] );
endmodule

// Imm Gen
// 把原本的 immediate extend 到 64 bits，只有 lw, sw, jal, jalr 會用到這個機制，其他可以直接 default
module Imm_Gen(Imm_Gen, Imm);
input [31:0] Imm;
output reg [31:0] Imm_Gen ;
reg [6:0] Opcode;

always@(*)
begin
    Opcode = Imm[6:0];
    case(Opcode)
    7'b0000011: //lw
    begin
        Imm_Gen[31:11] = {21{Imm[31]}} ;
        Imm_Gen[10:5] = Imm[30:25];
        Imm_Gen[4:1] = Imm[24:21];
        Imm_Gen[0] = Imm[20] ; 
    end
    7'b0100011: //sw
    begin
        Imm_Gen[31:11] = {21{Imm[31]}} ;
        Imm_Gen[10:5] = Imm[30:25];
        Imm_Gen[4:1] = Imm[11:8];
        Imm_Gen[0] = Imm[7] ;
    end
    7'b1101111: //jal
    begin
        Imm_Gen[31:20] = {12{Imm[31]}};
        Imm_Gen[19:12] = Imm[19:12];
        Imm_Gen[11] = Imm[20];
        Imm_Gen[10:5] = Imm[30:25];
        Imm_Gen[4:1] = Imm[24:21];
        Imm_Gen[0] = 1'b0;
    end
    7'b1100111: //jalr
    begin
        Imm_Gen[31:11] = {21{Imm[31]}} ;
        Imm_Gen[10:5] = Imm[30:25];
        Imm_Gen[4:1] = Imm[24:21];
        Imm_Gen[0] = Imm[20] ;
    end
    7'b1100011: //beq
    begin
        Imm_Gen[31:12] = {20{Imm[31]}} ;
        Imm_Gen[11] = Imm[7];
        Imm_Gen[10:5] = Imm[30:25];
        Imm_Gen[4:1] = Imm[11:8];
        Imm_Gen[0] = 0 ;
    end
    7'b0010011: //addi , slti
    begin
        Imm_Gen[31:11] = {21{Imm[31]}} ;
        Imm_Gen[10:5] = Imm[30:25];
        Imm_Gen[4:1] = Imm[24:21];
        Imm_Gen[0] = Imm[20] ;
    end
    default
    begin
        Imm_Gen = 0 ;
    end
    endcase
end
endmodule

// multiplxer for 32 bits
module Mux_32(Output, Input0, Input1, Control);
    input [31:0] Input0;
    input [31:0] Input1;
    input Control;
    output [31:0] Output;
    assign Output = Control ? Input1 : Input0; // Control == 0 => Input0, else => Input1
endmodule