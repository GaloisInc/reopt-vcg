def btw1 : instruction :=
  definst "btw" $ do
    pattern fun (v_3217 : imm int) (v_3220 : reg (bv 16)) => do
      v_6504 <- getRegister v_3220;
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_6504 (uvalueMInt (mi 16 (svalueMInt (bv_and (handleImmediateWithSignExtend v_3217 8 8) (expression.bv_nat 8 15)))))) 15 16);
      pure ()
    pat_end;
    pattern fun (v_3224 : reg (bv 16)) (v_3225 : reg (bv 16)) => do
      v_6517 <- getRegister v_3225;
      v_6518 <- getRegister v_3224;
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_6517 (uvalueMInt (mi 16 (svalueMInt (bv_and v_6518 (expression.bv_nat 16 15)))))) 15 16);
      pure ()
    pat_end;
    pattern fun (v_3209 : imm int) (v_3211 : Mem) => do
      v_9783 <- evaluateAddress v_3211;
      v_9784 <- eval (handleImmediateWithSignExtend v_3209 8 8);
      v_9789 <- load (add v_9783 (concat (expression.bv_nat 59 0) (bv_and (extract v_9784 0 5) (expression.bv_nat 5 1)))) 1;
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_9789 (uvalueMInt (concat (expression.bv_nat 5 0) (bv_and (extract v_9784 5 8) (expression.bv_nat 3 7))))) 7 8);
      pure ()
    pat_end;
    pattern fun (v_3215 : reg (bv 16)) (v_3214 : Mem) => do
      v_9801 <- evaluateAddress v_3214;
      v_9802 <- getRegister v_3215;
      v_9808 <- load (add v_9801 (concat (expression.bv_nat 3 0) (extract (mi 64 (svalueMInt v_9802)) 0 61))) 1;
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_9808 (uvalueMInt (concat (expression.bv_nat 5 0) (extract v_9802 13 16)))) 7 8);
      pure ()
    pat_end
