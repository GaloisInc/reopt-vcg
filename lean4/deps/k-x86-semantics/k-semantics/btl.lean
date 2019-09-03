def btl1 : instruction :=
  definst "btl" $ do
    pattern fun (v_3073 : imm int) (v_3076 : reg (bv 32)) => do
      v_6166 <- getRegister v_3076;
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_6166 (uvalueMInt (mi 32 (svalueMInt (bv_and (handleImmediateWithSignExtend v_3073 8 8) (expression.bv_nat 8 31)))))) 31 32);
      pure ()
    pat_end;
    pattern fun (v_3080 : reg (bv 32)) (v_3081 : reg (bv 32)) => do
      v_6179 <- getRegister v_3081;
      v_6180 <- getRegister v_3080;
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_6179 (uvalueMInt (mi 32 (svalueMInt (bv_and v_6180 (expression.bv_nat 32 31)))))) 31 32);
      pure ()
    pat_end;
    pattern fun (v_3065 : imm int) (v_3067 : Mem) => do
      v_9701 <- evaluateAddress v_3067;
      v_9702 <- eval (handleImmediateWithSignExtend v_3065 8 8);
      v_9707 <- load (add v_9701 (concat (expression.bv_nat 59 0) (bv_and (extract v_9702 0 5) (expression.bv_nat 5 3)))) 1;
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_9707 (uvalueMInt (concat (expression.bv_nat 5 0) (bv_and (extract v_9702 5 8) (expression.bv_nat 3 7))))) 7 8);
      pure ()
    pat_end;
    pattern fun (v_3071 : reg (bv 32)) (v_3070 : Mem) => do
      v_9719 <- evaluateAddress v_3070;
      v_9720 <- getRegister v_3071;
      v_9726 <- load (add v_9719 (concat (expression.bv_nat 3 0) (extract (mi 64 (svalueMInt v_9720)) 0 61))) 1;
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_9726 (uvalueMInt (concat (expression.bv_nat 5 0) (extract v_9720 29 32)))) 7 8);
      pure ()
    pat_end
