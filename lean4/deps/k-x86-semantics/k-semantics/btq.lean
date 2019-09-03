def btq1 : instruction :=
  definst "btq" $ do
    pattern fun (v_3091 : imm int) (v_3094 : reg (bv 64)) => do
      v_6200 <- getRegister v_3094;
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_6200 (uvalueMInt (mi 64 (svalueMInt (bv_and (handleImmediateWithSignExtend v_3091 8 8) (expression.bv_nat 8 63)))))) 63 64);
      pure ()
    pat_end;
    pattern fun (v_3098 : reg (bv 64)) (v_3099 : reg (bv 64)) => do
      v_6213 <- getRegister v_3099;
      v_6214 <- getRegister v_3098;
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_6213 (uvalueMInt (mi 64 (svalueMInt (bv_and v_6214 (expression.bv_nat 64 63)))))) 63 64);
      pure ()
    pat_end;
    pattern fun (v_3083 : imm int) (v_3085 : Mem) => do
      v_9737 <- evaluateAddress v_3085;
      v_9738 <- eval (handleImmediateWithSignExtend v_3083 8 8);
      v_9743 <- load (add v_9737 (concat (expression.bv_nat 59 0) (bv_and (extract v_9738 0 5) (expression.bv_nat 5 7)))) 1;
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_9743 (uvalueMInt (concat (expression.bv_nat 5 0) (bv_and (extract v_9738 5 8) (expression.bv_nat 3 7))))) 7 8);
      pure ()
    pat_end;
    pattern fun (v_3089 : reg (bv 64)) (v_3088 : Mem) => do
      v_9755 <- evaluateAddress v_3088;
      v_9756 <- getRegister v_3089;
      v_9760 <- load (add v_9755 (concat (expression.bv_nat 3 0) (extract v_9756 0 61))) 1;
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_9760 (uvalueMInt (concat (expression.bv_nat 5 0) (extract v_9756 61 64)))) 7 8);
      pure ()
    pat_end
