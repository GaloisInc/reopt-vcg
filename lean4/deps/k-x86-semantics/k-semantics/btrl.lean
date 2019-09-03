def btrl1 : instruction :=
  definst "btrl" $ do
    pattern fun (v_3109 : imm int) (v_3112 : reg (bv 32)) => do
      v_6234 <- getRegister v_3112;
      v_6239 <- eval (uvalueMInt (mi 32 (svalueMInt (bv_and (handleImmediateWithSignExtend v_3109 8 8) (expression.bv_nat 8 31)))));
      v_6243 <- eval (extract (shl (expression.bv_nat 32 1) v_6239) 0 32);
      setRegister (lhs.of_reg v_3112) (bv_and v_6234 (bv_xor v_6243 (mi (bitwidthMInt v_6243) -1)));
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_6234 v_6239) 31 32);
      pure ()
    pat_end;
    pattern fun (v_3116 : reg (bv 32)) (v_3117 : reg (bv 32)) => do
      v_6254 <- getRegister v_3117;
      v_6255 <- getRegister v_3116;
      v_6259 <- eval (uvalueMInt (mi 32 (svalueMInt (bv_and v_6255 (expression.bv_nat 32 31)))));
      v_6263 <- eval (extract (shl (expression.bv_nat 32 1) v_6259) 0 32);
      setRegister (lhs.of_reg v_3117) (bv_and v_6254 (bv_xor v_6263 (mi (bitwidthMInt v_6263) -1)));
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_6254 v_6259) 31 32);
      pure ()
    pat_end;
    pattern fun (v_3101 : imm int) (v_3103 : Mem) => do
      v_11180 <- evaluateAddress v_3103;
      v_11181 <- eval (handleImmediateWithSignExtend v_3101 8 8);
      v_11185 <- eval (add v_11180 (concat (expression.bv_nat 59 0) (bv_and (extract v_11181 0 5) (expression.bv_nat 5 3))));
      v_11186 <- load v_11185 1;
      v_11190 <- eval (uvalueMInt (concat (expression.bv_nat 5 0) (bv_and (extract v_11181 5 8) (expression.bv_nat 3 7))));
      v_11192 <- eval (extract (shl (expression.bv_nat 8 1) v_11190) 0 8);
      store v_11185 (bv_and v_11186 (bv_xor v_11192 (mi (bitwidthMInt v_11192) -1))) 1;
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_11186 v_11190) 7 8);
      pure ()
    pat_end;
    pattern fun (v_3107 : reg (bv 32)) (v_3106 : Mem) => do
      v_11205 <- evaluateAddress v_3106;
      v_11206 <- getRegister v_3107;
      v_11211 <- eval (add v_11205 (concat (expression.bv_nat 3 0) (extract (mi 64 (svalueMInt v_11206)) 0 61)));
      v_11212 <- load v_11211 1;
      v_11215 <- eval (uvalueMInt (concat (expression.bv_nat 5 0) (extract v_11206 29 32)));
      v_11217 <- eval (extract (shl (expression.bv_nat 8 1) v_11215) 0 8);
      store v_11211 (bv_and v_11212 (bv_xor v_11217 (mi (bitwidthMInt v_11217) -1))) 1;
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_11212 v_11215) 7 8);
      pure ()
    pat_end
