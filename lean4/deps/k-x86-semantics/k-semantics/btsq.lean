def btsq1 : instruction :=
  definst "btsq" $ do
    pattern fun (v_3181 : imm int) (v_3184 : reg (bv 64)) => do
      v_6420 <- getRegister v_3184;
      v_6425 <- eval (uvalueMInt (mi 64 (svalueMInt (bv_and (handleImmediateWithSignExtend v_3181 8 8) (expression.bv_nat 8 63)))));
      setRegister (lhs.of_reg v_3184) (bv_or v_6420 (extract (shl (expression.bv_nat 64 1) v_6425) 0 64));
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_6420 v_6425) 63 64);
      pure ()
    pat_end;
    pattern fun (v_3188 : reg (bv 64)) (v_3189 : reg (bv 64)) => do
      v_6437 <- getRegister v_3189;
      v_6438 <- getRegister v_3188;
      v_6442 <- eval (uvalueMInt (mi 64 (svalueMInt (bv_and v_6438 (expression.bv_nat 64 63)))));
      setRegister (lhs.of_reg v_3189) (bv_or v_6437 (extract (shl (expression.bv_nat 64 1) v_6442) 0 64));
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_6437 v_6442) 63 64);
      pure ()
    pat_end;
    pattern fun (v_3173 : imm int) (v_3175 : Mem) => do
      v_11372 <- evaluateAddress v_3175;
      v_11373 <- eval (handleImmediateWithSignExtend v_3173 8 8);
      v_11377 <- eval (add v_11372 (concat (expression.bv_nat 59 0) (bv_and (extract v_11373 0 5) (expression.bv_nat 5 7))));
      v_11378 <- load v_11377 1;
      v_11382 <- eval (uvalueMInt (concat (expression.bv_nat 5 0) (bv_and (extract v_11373 5 8) (expression.bv_nat 3 7))));
      store v_11377 (bv_or v_11378 (extract (shl (expression.bv_nat 8 1) v_11382) 0 8)) 1;
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_11378 v_11382) 7 8);
      pure ()
    pat_end;
    pattern fun (v_3179 : reg (bv 64)) (v_3178 : Mem) => do
      v_11394 <- evaluateAddress v_3178;
      v_11395 <- getRegister v_3179;
      v_11398 <- eval (add v_11394 (concat (expression.bv_nat 3 0) (extract v_11395 0 61)));
      v_11399 <- load v_11398 1;
      v_11402 <- eval (uvalueMInt (concat (expression.bv_nat 5 0) (extract v_11395 61 64)));
      store v_11398 (bv_or v_11399 (extract (shl (expression.bv_nat 8 1) v_11402) 0 8)) 1;
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_11399 v_11402) 7 8);
      pure ()
    pat_end
