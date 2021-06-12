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
    output reg        mem_wen_D  ;
    output reg [31:0] mem_addr_D ;
    output reg [31:0] mem_wdata_D;
    input  [31:0] mem_rdata_D;
    // For mem_I
    output reg [31:0] mem_addr_I ;
    input  [31:0] mem_rdata_I;
    
    //---------------------------------------//
    // Do not modify this part!!!            //
    // Exception: You may change wire to reg //
    reg    [31:0] PC          ;              //
    reg   [31:0] PC_nxt      ;              //
    reg          regWrite    ;              //
    reg   [ 4:0] rs1, rs2, rd;              //
    wire   [31:0] rs1_data    ;              //
    wire   [31:0] rs2_data    ;              //
    wire   [31:0] rd_data     ;              //
    //---------------------------------------//

    // Todo: other wire/reg
    reg [31:0] instruction ;
    reg [31:0] load_data ;
    reg [31:0] save_data ;
    reg [6:0] opcode ;
    // reg [4:0] read_addr1; // rs1 
    // reg [4:0] read_addr2; // rs2 
    // reg [4:0] write_addr; // rd 
    reg [31:0] Imm;
    // wire [31:0] busX; // rs1_data
    // wire [31:0] busY; // rs2_data
    wire [31:0] Imm_Gen;
    wire [31:0] ALU_result ;
    wire [31:0] ALU_In2 ;
    // wire [31:0] busW ; // rd_data
    wire [3:0] control ;
    wire [31:0] mux_out_1;
    wire [31:0] mux_out_2;
    // control signal
    wire zero;
    reg jalr, jal, branch, memread, memtoreg, memwrite, ALUSrc;
    reg auipc_or_not ;
    reg [4:2] ALUOp ;
    // PC signal
    reg [31:0] PC_4;
    // reg [4:0] PC;
    reg [31:0] PC_offset;
    reg [31:0] PC_jal;
    reg [31:0] PC_jalr;
    // reg [4:0] PC_nxt;
    reg jal_or_jalr;
    wire [63:0] mul_answer;
    wire mult_valid ;
    wire mult_ready ;
    wire mult_mode  ;

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
    // register register(.clk(clk),.reset(rst_n),.RegWrite(RegWrite),.RW(write_addr),.busW(busW),.RX(read_addr1),.RY(read_addr2),.busX(busX),.busY(busY));
    ALU ALU(.result(ALU_result), .zero(zero), .In1(rs1_data), .In2(ALU_In2), .control(control), .mult_valid(mult_valid), .mult_ready(mult_ready), .mul_answer(mul_answer));
    ALU_control ALU_control(.ALUOp(ALUOp), .bit_30(Imm[30]), .bit_25(Imm[25]), .function3(Imm[14:12]), .control(control));
    // mux_32 mux_before_ALU_1(.Out(ALU_In1), .In0(rs1_data), .In1(PC), .control(auipc));
    mux_32 mux_before_ALU_2(.Out(ALU_In2), .In0(rs2_data), .In1(Imm_Gen), .control(ALUSrc));
    mux_32 mux_after_data_memory(.Out(mux_out_1), .In0(ALU_result), .In1(load_data), .control(memtoreg));
    mux_32 mux_after_mux_for_jal(.Out(mux_out_2), .In0(mux_out_1), .In1(PC_4), .control(jal_or_jalr));
    mux_32 mux_after_mux_for_auipc(.Out(rd_data), .In0(mux_out_2), .In1(PC_offset), .control(auipc_or_not));
    Imm_Gen Imm_Gen_block(.Imm_Gen(Imm_Gen), .Imm(Imm));
    multDiv mymul(.clk(clk), .rst_n(rst_n), .valid(mult_valid), .ready(mult_ready), .mode(mult_mode), .in_A(rs1_data), .in_B(ALU_In2), .out(mul_answer));

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
        // total nine signals
        jalr = 0 ;
        jal = 0 ;
        branch = 0 ;
        memread = 0 ;
        memtoreg = 0 ;
        ALUOp = 3'b000 ;
        memwrite = 0 ;
        regWrite = 0 ;
        ALUSrc = 0 ;
        jal_or_jalr = 0 ;
        auipc_or_not = 0 ;
        case(opcode)
        7'b0110011: //and, sub, add, or, slt, mul
        begin
            jal_or_jalr = 0 ;
            jalr = 0 ;
            jal = 0 ;
            branch = 0 ;
            memread = 0 ;
            memtoreg = 0 ;
            memwrite = 0 ;
            if (mult_valid == 1 && mult_ready == 0) 
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

module multDiv(clk, rst_n, valid, ready, mode, in_A, in_B, out);
    // Todo: your HW3
    input         clk, rst_n;
    input         valid, mode; // mode: 0: multu, 1: divu
    input  [31:0] in_A, in_B;
    output reg [63:0] out;
    output reg        ready; 

    // Definition of states
    parameter IDLE = 2'b00;
    parameter MULT = 2'b01;
    parameter DIV  = 2'b10;
    parameter OUT  = 2'b11;

    // Todo: Wire and reg
    reg  [ 1:0] state, state_nxt;
    reg  [ 4:0] counter, counter_nxt;
    reg  [63:0] shreg, shreg_nxt;
    reg  [31:0] alu_in, alu_in_nxt;
    reg  [32:0] alu_out;

    // Todo 5: wire assignments
    reg [31:0] In1, In2;
    reg add;
    reg write_in;
    
    // Combinational always block
    // Todo 1: State machine
    always @(*) begin
        case(state)
            IDLE: 
            begin
                if (valid == 0) 
                    state_nxt = IDLE ;
                else if (valid == 1 && mode == 0)
                    state_nxt = MULT ;
                else if (valid == 1 && mode == 1) 
                    state_nxt = DIV ;
                else 
                    state_nxt = IDLE ;
            end
            MULT:
            begin
                if (counter != 31) 
                    state_nxt = MULT ;
                else begin
                    state_nxt = OUT ;
                end
            end
            DIV :
            begin
                if (counter != 31)
                    state_nxt = DIV ;
                else begin
                    state_nxt = OUT ;
                end
            end
            OUT : state_nxt = IDLE;
        endcase
    end

    // Todo 2: Counter
    // next_state
    always @(*)
    begin
        if (state == MULT || state == DIV)
        begin
            counter_nxt = counter + 1 ;
        end
        else 
        begin
            counter_nxt = 0 ;   
        end
    end
    // current_state
    always @(posedge clk)
    begin
        counter <= counter_nxt ;
    end


    // ALU input
    always @(*) 
    begin
        case(state)
            IDLE: 
            begin
                if (valid) 
                begin
                      alu_in_nxt = in_B;
                end
                else  alu_in_nxt = 0;
            end
            OUT : alu_in_nxt = 0;
            default: alu_in_nxt = alu_in;
        endcase
    end
    always @(posedge clk) 
    begin
        alu_in <= alu_in_nxt ;
    end
    // Todo 3: ALU output
    always@ (*)
    begin
        In1 = alu_in ;
        In2 = shreg[63:32];
    end

    always@ (*)
    begin
        case(state)
        MULT:
        begin
            if (add == 1)
                alu_out = In1 + In2 ;
            else 
                alu_out = {{1'b0},In2} ;
        end
        DIV:
        begin
            if (write_in == 1 )
                alu_out = In2 - In1 ;
            else begin
                alu_out = In2 ;
            end
        end
        default:
            alu_out = 0 ;
        endcase
    end
    // Todo 4: Shift register
    always @(*)
    begin
        if ( state == IDLE )
            shreg_nxt = {{32{1'b0}}, in_A};
        else 
        begin
            shreg_nxt = 0 ;
            if (state == MULT)
            begin
                shreg_nxt = {alu_out, shreg[31:1]};
            end
            else if (state == DIV)
            begin
                shreg_nxt = {alu_out[30:0], shreg[31:0], write_in};
            end
            else 
            begin
                shreg_nxt = 0 ;
            end
        end
    end
    //sequential
    always @(posedge clk)
    begin
        shreg <= shreg_nxt ;
    end

    // Todo: Sequential always block
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= IDLE;
        end
        else begin
            state <= state_nxt;
        end
    end

    // output control 
    reg [31:0] buffer_1 ;
    reg [31:0] buffer_2 ;
    always @(clk)
    begin
        ready = 0 ;
        out = 0 ;
        buffer_1 = 0 ;
        buffer_2 = 0 ; 
        if (counter == 31)
        begin
            ready = 1 ;
            if (state == MULT)
                out = shreg_nxt ;
            else if (state == DIV)
            begin
                if (shreg_nxt[63:32] >= In1)
                begin
                    buffer_1 = shreg_nxt[63:32] - In1 ;
                    buffer_2 = {shreg_nxt[30:0], 1'b1} ;
                    out = {buffer_1, buffer_2};
                end
                else begin
                    buffer_1 = shreg_nxt[63:32] ;
                    buffer_2 = {shreg_nxt[30:0], 1'b0};
                    out = {buffer_1, buffer_2} ;
                end
            end
            else begin
                
            end
        end
        else 
        begin
            ready = 0 ;
            out = 0 ;
        end 
    end

    // control 
    always @(*)
    begin
        add = 0 ;
        write_in = 0 ;
        if (state == MULT)
        begin
            if (shreg[0] == 1)
                add = 1 ;
            else begin
                add = 0 ; 
            end
        end
        else if (state == DIV)
        begin
            if ( In2 >= In1 )
            begin
                write_in = 1 ;
            end
            else begin
                write_in = 0 ;
            end
        end
        else
        begin
            
        end
    end
endmodule

module ALU(result, zero, In1, In2, control, mult_valid, mult_ready, mul_answer);
output reg [31:0] result;
output reg zero; //equal or not
input [31:0] In1, In2;
input [3:0] control ;
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
input [2:0] ALUOp ;
input [2:0] function3;
output [3:0] control ;
assign control[0] = ALUOp[2] & ALUOp[1] & (!ALUOp[0]) & function3[2];
assign control[1] = function3[1] & ALUOp[1];
assign control[2] = bit_25 & ALUOp[0] & ALUOp[1] & ALUOp[2] ;
assign control[3] = (!ALUOp[2]) | (bit_30 & ALUOp[2] & ALUOp[1] & ALUOp[0] );
endmodule

// Imm Gen
// only lw,sw,jal,jalr會用到這個機制，其他可以直接default
module Imm_Gen(Imm_Gen, Imm);
input [31:0] Imm;
output reg [31:0] Imm_Gen ;
reg [6:0] opcode;

always@(*)
begin
    opcode = Imm[6:0];
    case(opcode)
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

// mux for 32 bits
module mux_32(Out, In0, In1, control);
    input [31:0] In0, In1;
    input control ;
    output [31:0] Out ;
    assign Out = control ? In1 : In0 ;
endmodule

module mux_4_32(Out, In0, In1, control);
    input [31:0] In0;
    input [4:0] In1;
    input control ;
    output [31:0] Out ;
    wire [31:0] buffer ;
    assign  buffer = {25'b0, In1, 2'b0};
    assign Out = control ? buffer : In0 ;
endmodule