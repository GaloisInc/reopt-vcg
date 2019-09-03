def cmovs1 : instruction :=
  definst "cmovs" $ do
    pattern fun (v_3223 : Mem) (v_3222 : reg (bv 32)) => do
      v_9147 <- getRegister sf;
      v_9149 <- evaluateAddress v_3223;
      v_9150 <- load v_9149 4;
      v_9151 <- getRegister v_3222;
      setRegister (lhs.of_reg v_3222) (mux (eq v_9147 (expression.bv_nat 1 1)) v_9150 v_9151);
      pure ()
    pat_end;
    pattern fun (v_3239 : Mem) (v_3240 : reg (bv 64)) => do
      v_9154 <- getRegister sf;
      v_9156 <- evaluateAddress v_3239;
      v_9157 <- load v_9156 8;
      v_9158 <- getRegister v_3240;
      setRegister (lhs.of_reg v_3240) (mux (eq v_9154 (expression.bv_nat 1 1)) v_9157 v_9158);
      pure ()
    pat_end;
    pattern fun (v_3257 : Mem) (v_3256 : reg (bv 16)) => do
      v_9161 <- getRegister sf;
      v_9163 <- evaluateAddress v_3257;
      v_9164 <- load v_9163 2;
      v_9165 <- getRegister v_3256;
      setRegister (lhs.of_reg v_3256) (mux (eq v_9161 (expression.bv_nat 1 1)) v_9164 v_9165);
      pure ()
    pat_end
