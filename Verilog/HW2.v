module mulDiv(
    clk,
    rst_n,
    valid,
    ready,
    mode,
    in_A,
    in_B,
    out
);

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