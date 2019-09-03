def btq1 : instruction :=
  definst "btq" $ do
    pattern fun (v_3105 : imm int) (v_3107 : reg (bv 64)) => do
      v_6355 <- getRegister v_3107;
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_6355 (uvalueMInt (mi 64 (svalueMInt (bv_and (handleImmediateWithSignExtend v_3105 8 8) (expression.bv_nat 8 63)))))) 63 64);
      pure ()
    pat_end;
    pattern fun (v_3111 : reg (bv 64)) (v_3112 : reg (bv 64)) => do
      v_6368 <- getRegister v_3112;
      v_6369 <- getRegister v_3111;
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_6368 (uvalueMInt (mi 64 (svalueMInt (bv_and v_6369 (expression.bv_nat 64 63)))))) 63 64);
      pure ()
    pat_end;
    pattern fun (v_3098 : imm int) (v_3097 : Mem) => do
      v_10024 <- evaluateAddress v_3097;
      v_10025 <- eval (handleImmediateWithSignExtend v_3098 8 8);
      v_10030 <- load (add v_10024 (concat (expression.bv_nat 59 0) (bv_and (extract v_10025 0 5) (expression.bv_nat 5 7)))) 1;
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_10030 (uvalueMInt (concat (expression.bv_nat 5 0) (bv_and (extract v_10025 5 8) (expression.bv_nat 3 7))))) 7 8);
      pure ()
    pat_end;
    pattern fun (v_3102 : reg (bv 64)) (v_3101 : Mem) => do
      v_10042 <- evaluateAddress v_3101;
      v_10043 <- getRegister v_3102;
      v_10047 <- load (add v_10042 (concat (expression.bv_nat 3 0) (extract v_10043 0 61))) 1;
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_10047 (uvalueMInt (concat (expression.bv_nat 5 0) (extract v_10043 61 64)))) 7 8);
      pure ()
    pat_end
