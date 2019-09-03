def btcl1 : instruction :=
  definst "btcl" $ do
    pattern fun (v_3033 : imm int) (v_3035 : reg (bv 32)) => do
      v_6195 <- getRegister v_3035;
      v_6200 <- eval (uvalueMInt (mi 32 (svalueMInt (bv_and (handleImmediateWithSignExtend v_3033 8 8) (expression.bv_nat 8 31)))));
      setRegister (lhs.of_reg v_3035) (bv_xor v_6195 (extract (shl (expression.bv_nat 32 1) v_6200) 0 32));
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_6195 v_6200) 31 32);
      pure ()
    pat_end;
    pattern fun (v_3039 : reg (bv 32)) (v_3040 : reg (bv 32)) => do
      v_6212 <- getRegister v_3040;
      v_6213 <- getRegister v_3039;
      v_6217 <- eval (uvalueMInt (mi 32 (svalueMInt (bv_and v_6213 (expression.bv_nat 32 31)))));
      setRegister (lhs.of_reg v_3040) (bv_xor v_6212 (extract (shl (expression.bv_nat 32 1) v_6217) 0 32));
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_6212 v_6217) 31 32);
      pure ()
    pat_end;
    pattern fun (v_3026 : imm int) (v_3025 : Mem) => do
      v_11333 <- evaluateAddress v_3025;
      v_11334 <- eval (handleImmediateWithSignExtend v_3026 8 8);
      v_11338 <- eval (add v_11333 (concat (expression.bv_nat 59 0) (bv_and (extract v_11334 0 5) (expression.bv_nat 5 3))));
      v_11339 <- load v_11338 1;
      v_11343 <- eval (uvalueMInt (concat (expression.bv_nat 5 0) (bv_and (extract v_11334 5 8) (expression.bv_nat 3 7))));
      store v_11338 (bv_xor v_11339 (extract (shl (expression.bv_nat 8 1) v_11343) 0 8)) 1;
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_11339 v_11343) 7 8);
      pure ()
    pat_end;
    pattern fun (v_3030 : reg (bv 32)) (v_3029 : Mem) => do
      v_11355 <- evaluateAddress v_3029;
      v_11356 <- getRegister v_3030;
      v_11360 <- eval (add v_11355 (concat (expression.bv_nat 3 0) (extract (leanSignExtend v_11356 64) 0 61)));
      v_11361 <- load v_11360 1;
      v_11364 <- eval (uvalueMInt (concat (expression.bv_nat 5 0) (extract v_11356 29 32)));
      store v_11360 (bv_xor v_11361 (extract (shl (expression.bv_nat 8 1) v_11364) 0 8)) 1;
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_11361 v_11364) 7 8);
      pure ()
    pat_end
