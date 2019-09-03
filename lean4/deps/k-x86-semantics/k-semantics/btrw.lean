def btrw1 : instruction :=
  definst "btrw" $ do
    pattern fun (v_3145 : imm int) (v_3148 : reg (bv 16)) => do
      v_6330 <- getRegister v_3148;
      v_6335 <- eval (uvalueMInt (mi 16 (svalueMInt (bv_and (handleImmediateWithSignExtend v_3145 8 8) (expression.bv_nat 8 15)))));
      v_6339 <- eval (extract (shl (expression.bv_nat 16 1) v_6335) 0 16);
      setRegister (lhs.of_reg v_3148) (bv_and v_6330 (bv_xor v_6339 (mi (bitwidthMInt v_6339) -1)));
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_6330 v_6335) 15 16);
      pure ()
    pat_end;
    pattern fun (v_3152 : reg (bv 16)) (v_3153 : reg (bv 16)) => do
      v_6350 <- getRegister v_3153;
      v_6351 <- getRegister v_3152;
      v_6355 <- eval (uvalueMInt (mi 16 (svalueMInt (bv_and v_6351 (expression.bv_nat 16 15)))));
      v_6359 <- eval (extract (shl (expression.bv_nat 16 1) v_6355) 0 16);
      setRegister (lhs.of_reg v_3153) (bv_and v_6350 (bv_xor v_6359 (mi (bitwidthMInt v_6359) -1)));
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_6350 v_6355) 15 16);
      pure ()
    pat_end;
    pattern fun (v_3137 : imm int) (v_3139 : Mem) => do
      v_11278 <- evaluateAddress v_3139;
      v_11279 <- eval (handleImmediateWithSignExtend v_3137 8 8);
      v_11283 <- eval (add v_11278 (concat (expression.bv_nat 59 0) (bv_and (extract v_11279 0 5) (expression.bv_nat 5 1))));
      v_11284 <- load v_11283 1;
      v_11288 <- eval (uvalueMInt (concat (expression.bv_nat 5 0) (bv_and (extract v_11279 5 8) (expression.bv_nat 3 7))));
      v_11290 <- eval (extract (shl (expression.bv_nat 8 1) v_11288) 0 8);
      store v_11283 (bv_and v_11284 (bv_xor v_11290 (mi (bitwidthMInt v_11290) -1))) 1;
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_11284 v_11288) 7 8);
      pure ()
    pat_end;
    pattern fun (v_3143 : reg (bv 16)) (v_3142 : Mem) => do
      v_11303 <- evaluateAddress v_3142;
      v_11304 <- getRegister v_3143;
      v_11309 <- eval (add v_11303 (concat (expression.bv_nat 3 0) (extract (mi 64 (svalueMInt v_11304)) 0 61)));
      v_11310 <- load v_11309 1;
      v_11313 <- eval (uvalueMInt (concat (expression.bv_nat 5 0) (extract v_11304 13 16)));
      v_11315 <- eval (extract (shl (expression.bv_nat 8 1) v_11313) 0 8);
      store v_11309 (bv_and v_11310 (bv_xor v_11315 (mi (bitwidthMInt v_11315) -1))) 1;
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_11310 v_11313) 7 8);
      pure ()
    pat_end
